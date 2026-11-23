//! Support for caching and keeping send & receive window.

use std::cmp::{max, min};
use std::collections::{BTreeMap, HashSet, VecDeque};
use std::fmt::{self, Display};
use std::io::{Error, ErrorKind, Result};
use std::ops::Bound::Included;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Duration;

use super::Timer;

/// An aggregate budget for growable receive windows owned by one redirector.
#[derive(Debug)]
pub struct CacheBudget {
    used: AtomicUsize,
    limit: usize,
}

impl CacheBudget {
    pub fn new(limit: usize) -> CacheBudget {
        CacheBudget { used: AtomicUsize::new(0), limit }
    }

    pub(crate) fn reserve(&self, bytes: usize) -> Result<()> {
        self.used.try_update(Ordering::Relaxed, Ordering::Relaxed, |used| {
            used.checked_add(bytes).filter(|&next| next <= self.limit)
        }).map_err(|_| Error::new(ErrorKind::OutOfMemory, "TCP cache budget exceeded"))?;
        Ok(())
    }

    pub(crate) fn release(&self, bytes: usize) {
        self.used.fetch_sub(bytes, Ordering::Relaxed);
    }

    pub(crate) fn remaining(&self) -> usize {
        self.limit.saturating_sub(self.used.load(Ordering::Relaxed))
    }
}

/// Represents the max distance of u32 values between packets in an u32 window.
const MAX_U32_WINDOW_SIZE: usize = 16 * 1024 * 1024;

/// Represents if the buffer should be allocated in the initial constructor of caches.
const ALLOC_IN_INITIAL: bool = false;

/// Represents a queue cache. The `Queue` can hold continuous bytes constantly unless they are
/// invalidated. The `Queue` can be used as a send window of a TCP connection.
#[derive(Debug)]
pub struct Queue {
    buffer: Vec<u8>,
    capacity: usize,
    sequence: u32,
    head: usize,
    size: usize,
    clocks: VecDeque<(u32, Timer)>,
    retrans: Option<u32>,
}

#[allow(clippy::unnecessary_lazy_evaluations)]
impl Queue {
    /// Creates a new `Queue`.
    #[deprecated = "Use with_capacity instead"]
    pub fn new(sequence: u32) -> Queue {
        Queue::with_capacity(usize::MAX, sequence)
    }

    /// Creates a new `Queue` with the specified capacity.
    pub fn with_capacity(capacity: usize, sequence: u32) -> Queue {
        Queue {
            buffer: match ALLOC_IN_INITIAL {
                true => Vec::with_capacity(capacity),
                false => Vec::new(),
            },
            capacity,
            sequence,
            head: 0,
            size: 0,
            clocks: match ALLOC_IN_INITIAL {
                true => VecDeque::with_capacity(capacity),
                false => VecDeque::new(),
            },
            retrans: None,
        }
    }

    /// Appends some bytes to the end of the queue.
    pub fn append(&mut self, payload: &[u8], rto: u64) -> Result<()> {
        if payload.len() > self.remaining() {
            return Err(Error::new(ErrorKind::Other, "queue is full"));
        }
        if payload.len() > self.buffer.len() - self.size {
            // Extend the buffer
            let prev_len = self.buffer.len();
            let prev_tail = self.tail();
            let new_len = min(
                self.capacity,
                max(
                    self.buffer
                        .len()
                        .checked_add(self.buffer.len() / 2)
                        .unwrap_or(usize::MAX),
                    self.size + payload.len(),
                ),
            );
            self.buffer.resize(new_len, 0);

            // From the begin of the buffer to the tail
            if prev_tail <= self.head {
                // From the begin to the mid of the buffer
                let len_a = min(prev_tail, new_len - prev_len);
                self.buffer.copy_within(..len_a, prev_len);

                // From the mid to the tail of the buffer
                let len_b = prev_tail - len_a;
                if len_b > 0 {
                    self.buffer.copy_within(len_a..len_a + len_b, 0);
                }
            }
        }

        // Sequence and clock
        let sequence = self.sequence.wrapping_add(self.size as u32);
        self.clocks.push_back((sequence, Timer::new(rto)));

        // From the tail to the end of the buffer
        let tail = self.tail();
        let len_a = min(self.buffer.len() - tail, payload.len());
        self.buffer[tail..tail + len_a].copy_from_slice(&payload[..len_a]);

        // From the begin of the buffer to the head
        let len_b = payload.len() - len_a;
        if len_b > 0 {
            self.buffer[..len_b].copy_from_slice(&payload[len_a..]);
        }

        self.size += payload.len();

        Ok(())
    }

    /// Invalidates queue to the certain sequence and returns the RTT.
    pub fn invalidate_to(&mut self, sequence: u32) -> Option<Duration> {
        let size = sequence.wrapping_sub(self.sequence) as usize;

        // Only ACK bytes actually enqueued, not future sequence numbers.
        if size <= self.size {
            self.sequence = sequence;
            self.size = self.size.saturating_sub(size);
            if self.size == 0 {
                self.head = 0;
            } else {
                self.head = (self.head + (size % self.buffer.len())) % self.buffer.len();
            }

            let mut rtt = None;

            // Pop clocks
            while !self.clocks.is_empty() {
                let dist = sequence.wrapping_sub(self.clocks[0].0) as usize;
                let recv_next = match self.clocks.len() {
                    1 => self.recv_next(),
                    _ => self.clocks[1].0,
                };
                let dist_next = sequence.wrapping_sub(recv_next) as usize;

                if dist <= MAX_U32_WINDOW_SIZE as usize && dist_next <= MAX_U32_WINDOW_SIZE as usize
                {
                    let clock = self.clocks.pop_front().unwrap();
                    let timer = clock.1;
                    if !timer.is_timedout() {
                        // Choose the largest RTT
                        if rtt.is_none() {
                            rtt = Some(timer.elapsed());

                            // Rollback on retransmission
                            if let Some(retrans) = self.retrans {
                                if retrans.wrapping_sub(sequence) as usize
                                    <= MAX_U32_WINDOW_SIZE
                                {
                                    // Karn's algorithm
                                    rtt = None;
                                }
                            }
                        }
                    }
                } else if dist <= MAX_U32_WINDOW_SIZE {
                    let instant = self.clocks[0].1;
                    self.clocks.pop_front();
                    self.clocks.push_front((sequence, instant));
                    break;
                } else {
                    break;
                }
            }

            // Retransmission
            if let Some(retrans) = self.retrans {
                if self.sequence.wrapping_sub(retrans) as usize
                    <= MAX_U32_WINDOW_SIZE
                {
                    self.retrans = None;
                }
            }

            return rtt;
        }

        None
    }

    /// Advances the SYN sequence number while the data queue is empty.
    pub fn advance_empty(&mut self, sequence: u32) {
        if self.size == 0 {
            self.sequence = sequence;
        }
    }

    /// Returns the payload from the certain sequence of the queue in the given size.
    pub fn get(&self, sequence: u32, size: usize) -> Result<Vec<u8>> {
        if size == 0 {
            return Ok(Vec::new());
        }
        let distance = sequence.wrapping_sub(self.sequence) as usize;
        if distance > self.size {
            return Err(Error::new(
                ErrorKind::InvalidInput,
                "queue at the certain sequence does not exist",
            ));
        }
        if self.size - distance < size {
            return Err(Error::new(ErrorKind::InvalidInput, "request size too big"));
        }

        let mut payload = vec![0u8; size];

        // From the head to the end of the buffer
        let head = self.head + distance;
        let head = head.checked_sub(self.buffer.len()).unwrap_or(head);
        let length_a = min(size, self.buffer.len() - head);
        payload[..length_a].copy_from_slice(&self.buffer[head..head + length_a]);

        // From the begin of the buffer to the tail
        let length_b = size - length_a;
        if length_b > 0 {
            payload[length_a..].copy_from_slice(&self.buffer[..length_b]);
        }

        Ok(payload)
    }

    /// Returns all the payload of the queue.
    pub fn get_all(&self) -> Vec<u8> {
        self.get(self.sequence, self.size).unwrap()
    }

    /// Returns the payload which is timed out from the begin to the first byte which is not timed out.
    #[deprecated = "use get_timed_out_and_update instead"]
    pub fn get_timed_out(&self) -> Vec<u8> {
        let mut recv_next = None;
        for clock in &self.clocks {
            let timer = clock.1;
            if !timer.is_timedout() {
                recv_next = Some(clock.0);
                break;
            }
        }

        match recv_next {
            Some(recv_next) => {
                let size = recv_next.wrapping_sub(self.sequence) as usize;

                self.get(self.sequence, size).unwrap()
            }
            None => self.get_all(),
        }
    }

    /// Returns the payload which is timed out from the begin to the first byte which is not timed out
    /// and update their timeout timer.
    pub fn get_timed_out_and_update(&mut self, rto: u64) -> Vec<u8> {
        let mut recv_next = None;
        for clock in &self.clocks {
            let timer = clock.1;
            if !timer.is_timedout() {
                recv_next = Some(clock.0);
                break;
            }
        }

        match recv_next {
            Some(recv_next) => {
                let size = recv_next.wrapping_sub(self.sequence) as usize;

                // Update clock
                while !self.clocks.is_empty() {
                    let next_sequence = self.clocks.front().unwrap().0;
                    if recv_next.wrapping_sub(next_sequence) as usize
                        <= MAX_U32_WINDOW_SIZE
                    {
                        self.clocks.pop_front();
                    } else {
                        self.clocks.push_front((self.sequence, Timer::new(rto)));

                        break;
                    }
                }
                self.retrans = Some(recv_next);

                self.get(self.sequence, size).unwrap()
            }
            None => {
                // Update clock
                self.clocks.clear();
                self.clocks.push_back((self.sequence, Timer::new(rto)));
                self.retrans = Some(self.recv_next());

                self.get_all()
            }
        }
    }

    /// Returns the capacity of the queue.
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Returns the sequence of the queue.
    pub fn sequence(&self) -> u32 {
        self.sequence
    }

    /// Returns the length of the queue.
    pub fn len(&self) -> usize {
        self.size
    }

    /// Returns the remaining size of the window.
    pub fn remaining(&self) -> usize {
        self.capacity - self.size
    }

    fn tail(&self) -> usize {
        self.head
            .checked_add(self.size)
            .unwrap_or_else(|| self.size - (self.buffer.len() - self.head))
            .checked_rem(self.buffer.len())
            .unwrap_or(0)
    }

    /// Returns the receive next of the queue.
    pub fn recv_next(&self) -> u32 {
        self.sequence.wrapping_add(self.size as u32)
    }

    /// Returns if the queue is empty.
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }
}

impl Display for Queue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let head = self.head;
        // The second checked_sub will only fall on 0 if the length of the buffer is 0
        let tail = self
            .tail()
            .checked_sub(1)
            .unwrap_or_else(|| self.buffer.len().saturating_sub(1));

        write!(f, "[")?;
        for i in 0..self.buffer.len() {
            if i != 0 {
                write!(f, ", ")?;
            }

            if i == head {
                write!(f, "<")?;
            }
            write!(f, "{}", self.buffer[i])?;
            if i == tail {
                write!(f, ">")?;
            }
        }
        write!(f, "]")
    }
}

#[test]
fn queue_new() {
    let q = Queue::with_capacity(0, 0);
    assert_eq!(q.to_string(), "[]");
}

#[test]
fn queue_append_overflow() {
    let mut q = Queue::with_capacity(9, 0);

    let v = (0..8).into_iter().collect::<Vec<_>>();
    q.append(v.as_slice(), 0).unwrap();

    q.invalidate_to(2);

    let v = (8..10).into_iter().collect::<Vec<_>>();
    q.append(v.as_slice(), 0).unwrap();

    q.invalidate_to(6);

    let v = (10..15).into_iter().collect::<Vec<_>>();
    q.append(v.as_slice(), 0).unwrap();

    assert_eq!(q.to_string(), "[9, 10, 11, 12, 13, 14>, <6, 7, 8]");
}

#[test]
fn queue_append_overflow_overlapped() {
    let mut q = Queue::with_capacity(9, 0);

    let v = (0..8).into_iter().collect::<Vec<_>>();
    q.append(v.as_slice(), 0).unwrap();

    q.invalidate_to(3);

    let v = (8..11).into_iter().collect::<Vec<_>>();
    q.append(v.as_slice(), 0).unwrap();

    q.invalidate_to(6);

    let v = (11..15).into_iter().collect::<Vec<_>>();
    q.append(v.as_slice(), 0).unwrap();

    assert_eq!(q.to_string(), "[9, 10, 11, 12, 13, 14>, <6, 7, 8]");
}

#[test]
fn queue_append_overflow_overlapped_2() {
    let mut q = Queue::with_capacity(9, 0);

    let v = (0..8).into_iter().collect::<Vec<_>>();
    q.append(v.as_slice(), 0).unwrap();

    q.invalidate_to(6);

    let v = (8..14).into_iter().collect::<Vec<_>>();
    q.append(v.as_slice(), 0).unwrap();

    let v = (14..15).into_iter().collect::<Vec<_>>();
    q.append(v.as_slice(), 0).unwrap();

    assert_eq!(q.to_string(), "[9, 10, 11, 12, 13, 14>, <6, 7, 8]");
}

/// Represents a window cache. The `Window` can hold discontinuous bytes and pop out them when
/// they are completed. The `Window` can be used as a receive window of a TCP connection.
#[derive(Debug)]
pub struct Window {
    buffer: Vec<u8>,
    capacity: usize,
    sequence: u32,
    head: usize,
    /// Represents the expected size from the head to the tail. NOT all the bytes in [head, head + size) are filled.
    size: usize,
    /// Represents edges of filled values. Use an u64 instead of an u32 because the sequence is used as a ring.
    edges: BTreeMap<u64, usize>,
    budget: Option<Arc<CacheBudget>>,
}

impl Drop for Window {
    fn drop(&mut self) {
        if let Some(budget) = &self.budget {
            budget.release(self.buffer.len());
        }
    }
}

impl Window {
    /// Creates a new `Window`.
    #[deprecated = "Use with_capacity instead"]
    pub fn new(sequence: u32) -> Window {
        Window::with_capacity(usize::MAX, sequence)
    }

    /// Creates a new `Window` with the specified capacity.
    pub fn with_capacity(capacity: usize, sequence: u32) -> Window {
        Window {
            buffer: match ALLOC_IN_INITIAL {
                true => Vec::with_capacity(capacity),
                false => Vec::new(),
            },
            capacity,
            sequence,
            head: 0,
            size: 0,
            edges: BTreeMap::new(),
            budget: None,
        }
    }

    /// Assign the shared memory budget before the window receives data.
    pub fn set_budget(&mut self, budget: Arc<CacheBudget>) {
        debug_assert!(self.buffer.is_empty() && self.budget.is_none());
        self.budget = Some(budget);
    }

    /// Appends some bytes to the window and returns continuous bytes from the beginning.
    #[allow(clippy::unnecessary_lazy_evaluations)]
    pub fn append(&mut self, sequence: u32, payload: &[u8]) -> Result<Option<Vec<u8>>> {
        let sub_sequence = sequence.wrapping_sub(self.sequence) as usize;
        let (sequence, payload, sub_sequence) = if sub_sequence > MAX_U32_WINDOW_SIZE {
            let recv_next = sequence.wrapping_add(payload.len() as u32);
            let sub_recv_next_to_sequence = recv_next.wrapping_sub(self.sequence);

            if sub_recv_next_to_sequence as usize <= MAX_U32_WINDOW_SIZE {
                let sub_sequence = self.sequence.wrapping_sub(sequence);
                (self.sequence, &payload[sub_sequence as usize..], 0)
            } else {
                return Ok(None);
            }
        } else {
            (sequence, payload, sub_sequence)
        };

        let size = sub_sequence + payload.len();
        if size > self.capacity {
            return Err(Error::new(ErrorKind::Other, "window is full"));
        }
        if size > self.buffer.len() {
            // Extend the buffer
            let prev_len = self.buffer.len();
            let new_len = min(
                self.capacity,
                max(
                    self.buffer
                        .len()
                        .checked_add(self.buffer.len() / 2)
                        .unwrap_or(usize::MAX),
                    size,
                ),
            );
            if let Some(budget) = &self.budget {
                budget.reserve(new_len - prev_len)?;
            }
            self.buffer.resize(new_len, 0);

            // From the begin of the buffer to the tail
            let ranges = self
                .edges
                .iter()
                .map(|(sequence, &size)| {
                    let sub_sequence = if *sequence >= self.sequence as u64 {
                        *sequence - self.sequence as u64
                    } else {
                        *sequence + (1u64 << 32) - self.sequence as u64
                    } as usize;
                    let mut begin = self.get_tail(self.head, sub_sequence, prev_len);
                    let end = self.get_tail(begin, size, prev_len);
                    if end <= begin {
                        begin = 0;
                    }

                    (begin, end)
                })
                .filter(|(begin, end)| *begin < self.head || *end <= self.head)
                .collect::<Vec<_>>();
            for (begin, end) in ranges {
                // From the begin to the mid of the buffer
                let len_a = min(
                    (new_len - prev_len).saturating_sub(begin),
                    end - begin,
                );
                if len_a > 0 {
                    self.buffer
                        .copy_within(begin..begin + len_a, prev_len + begin);
                }

                // From the mid to the tail of the buffer
                let len_b = (end - begin) - len_a;
                if len_b > 0 {
                    self.buffer
                        .copy_within(begin + len_a..end, begin + len_a - (new_len - prev_len));
                }
            }
        }

        // TODO: copy valid bytes only
        // TODO: copy bytes into empty ranges only
        // To the end of the buffer
        let tail = self.get_tail(self.head, sub_sequence, self.buffer.len());
        let len_a = min(self.buffer.len() - tail, payload.len());
        self.buffer[tail..tail + len_a].copy_from_slice(&payload[..len_a]);

        // From the begin of the buffer
        let len_b = payload.len() - len_a;
        if len_b > 0 {
            self.buffer[..len_b].copy_from_slice(&payload[len_a..]);
        }

        // Update size
        let recv_next = sequence.wrapping_add(payload.len() as u32);
        let record_recv_next = self.sequence.wrapping_add(self.size as u32);
        let sub_recv_next = recv_next.wrapping_sub(record_recv_next);
        if sub_recv_next as usize <= MAX_U32_WINDOW_SIZE {
            self.size += sub_recv_next as usize;
        }

        // Insert and merge ranges
        {
            let mut sequence = sequence as u64;
            if (sequence as u32) < self.sequence {
                sequence += 1u64 << 32;
            }

            // Select ranges which can be merged in a loop
            let mut end = sequence + payload.len() as u64;
            loop {
                let mut pop_keys = Vec::new();
                for (&key, &value) in self.edges.range((
                    Included(&sequence),
                    Included(&(sequence + payload.len() as u64)),
                )) {
                    pop_keys.push(key);
                    end = max(end, key + value as u64);
                }

                if pop_keys.is_empty() {
                    break;
                }

                // Pop
                for ref pop_key in pop_keys {
                    self.edges.remove(pop_key);
                }
            }

            // Select the previous range if exists
            let mut prev_key = None;
            for &key in self.edges.keys() {
                if key < sequence {
                    prev_key = Some(key);
                }
            }

            // Merge previous range without losing its existing right edge.
            // Remove the old entry so there is exactly one merged range.
            if let Some(prev_key) = prev_key {
                let prev_end = prev_key + *self.edges.get(&prev_key).unwrap() as u64;
                if prev_end >= sequence {
                    end = max(end, prev_end);
                    sequence = prev_key;
                    self.edges.remove(&prev_key);
                }
            }

            // Insert range
            self.edges.insert(sequence, (end - sequence) as usize);
        }

        // Pop if possible
        let first_key = *self.edges.keys().next().unwrap();
        if first_key as u32 == self.sequence {
            let size = self.edges.remove(&first_key).unwrap();

            // Shrink range sequence is possible
            if ((u32::MAX - self.sequence) as usize) < size {
                let keys = self.edges.keys().copied().collect::<Vec<_>>();

                for key in keys {
                    let value = self.edges.remove(&key).unwrap();
                    let normalized = if key >= (1u64 << 32) {
                        key - (1u64 << 32)
                    } else {
                        key
                    };
                    self.edges.insert(normalized, value);
                }
            }

            // Continuous payload
            let mut cont_payload = vec![0u8; size];

            // From the head to the end of the buffer
            let len_a = min(size, self.buffer.len() - self.head);
            cont_payload[..len_a].copy_from_slice(&self.buffer[self.head..self.head + len_a]);

            // From the begin of the buffer to the tail
            let len_b = size - len_a;
            if len_b > 0 {
                cont_payload[len_a..].copy_from_slice(&self.buffer[..len_b]);
            }

            self.sequence = self.sequence.wrapping_add(size as u32);
            self.head = (self.head + (size % self.buffer.len())) % self.buffer.len();
            self.size -= cont_payload.len();

            return Ok(Some(cont_payload));
        }

        Ok(None)
    }

    /// Returns the sequence of the window.
    pub fn sequence(&self) -> u32 {
        self.sequence
    }

    /// Returns the length of the window. Not all bytes in [sequence, sequence + len) are filled.
    pub fn len(&self) -> usize {
        self.size
    }

    /// Returns the receive next of the window.
    #[allow(clippy::unnecessary_lazy_evaluations)]
    pub fn recv_next(&self) -> u32 {
        self.sequence.wrapping_add(self.size as u32)
    }

    /// Returns the remaining size of the window.
    pub fn remaining(&self) -> usize {
        self.capacity - self.size
    }

    fn tail(&self) -> usize {
        self.get_tail(self.head, self.size, self.buffer.len())
    }

    #[allow(clippy::unnecessary_lazy_evaluations)]
    fn get_tail(&self, head: usize, size: usize, max: usize) -> usize {
        let mod_sub_sequence = size.checked_rem(max).unwrap_or(0);
        head.checked_add(mod_sub_sequence)
            .unwrap_or_else(|| mod_sub_sequence - (max - head))
            .checked_rem(max)
            .unwrap_or(0)
    }

    /// Returns the filled edges of the window.
    #[allow(clippy::unnecessary_lazy_evaluations)]
    pub fn filled(&self) -> Vec<(u32, u32)> {
        let mut v = Vec::new();
        for (&sequence, &size) in &self.edges {
            let begin = sequence as u32;
            let end = begin.wrapping_add(size as u32);
            v.push((begin, end));
        }

        v
    }

    /// Returns if the window is empty.
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }
}

impl Display for Window {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let head = self.head;
        // The second checked_sub will only fall on 0 if the length of the buffer is 0
        let tail = self
            .tail()
            .checked_sub(1)
            .unwrap_or_else(|| self.buffer.len().saturating_sub(1));

        let mut edge_begin_set = HashSet::new();
        let mut edge_end_set = HashSet::new();
        self.edges.iter().for_each(|(sequence, &size)| {
            let sub_sequence = if *sequence >= self.sequence as u64 {
                *sequence - self.sequence as u64
            } else {
                *sequence + (1u64 << 32) - self.sequence as u64
            } as usize;
            let begin = self.get_tail(head, sub_sequence, self.buffer.len());
            let end = self
                .get_tail(begin, size, self.buffer.len())
                .checked_sub(1)
                .unwrap_or(self.buffer.len() - 1);
            edge_begin_set.insert(begin);
            edge_end_set.insert(end);
        });

        write!(f, "[")?;
        for i in 0..self.buffer.len() {
            if i != 0 {
                write!(f, ", ")?;
            }

            if i == head {
                write!(f, "<")?;
            }
            if edge_begin_set.contains(&i) {
                write!(f, "<")?;
            }
            write!(f, "{}", self.buffer[i])?;
            if edge_end_set.contains(&i) {
                write!(f, ">")?;
            }
            if i == tail {
                write!(f, ">")?;
            }
        }
        write!(f, "]")
    }
}

#[test]
fn window_new() {
    let w = Window::with_capacity(0, 0);
    assert_eq!(w.to_string(), "[]");
}

#[test]
fn shared_receive_budget_is_released() {
    let budget = Arc::new(CacheBudget::new(8));
    let mut window = Window::with_capacity(32, 0);
    window.set_budget(Arc::clone(&budget));
    assert!(window.append(2, &[2, 3, 4, 5, 6, 7]).unwrap().is_none());
    assert_eq!(budget.used.load(Ordering::Relaxed), 8);
    assert!(window.append(8, &[8]).is_err());
    drop(window);
    assert_eq!(budget.used.load(Ordering::Relaxed), 0);
}

#[test]
fn queue_and_window_wrap_across_zero() {
    let mut queue = Queue::with_capacity(32, u32::MAX - 1);
    queue.append(&[1, 2, 3], 1000).unwrap();
    assert_eq!(queue.recv_next(), 1);
    assert_eq!(queue.get(u32::MAX, 2).unwrap(), vec![2, 3]);
    queue.invalidate_to(1);
    assert_eq!(queue.len(), 0);

    let mut window = Window::with_capacity(32, u32::MAX - 1);
    assert_eq!(window.append(u32::MAX - 1, &[1, 2, 3]).unwrap(), Some(vec![1, 2, 3]));
    assert_eq!(window.sequence(), 1);
}

#[test]
fn overlapping_fragment_does_not_shrink_cached_range() {
    let mut w = Window::with_capacity(64, 0);
    assert!(w.append(10, &(10..20).collect::<Vec<_>>()).unwrap().is_none());
    assert!(w.append(15, &(15..18).collect::<Vec<_>>()).unwrap().is_none());
    let completed = w.append(0, &(0..10).collect::<Vec<_>>()).unwrap();
    assert_eq!(completed, Some((0..20).collect::<Vec<_>>()));
}

#[test]
fn overlapping_fragment_extends_cached_range() {
    let mut w = Window::with_capacity(64, 0);
    assert!(w.append(10, &(10..20).collect::<Vec<_>>()).unwrap().is_none());
    assert!(w.append(15, &(15..25).collect::<Vec<_>>()).unwrap().is_none());
    let completed = w.append(0, &(0..10).collect::<Vec<_>>()).unwrap();
    assert_eq!(completed, Some((0..25).collect::<Vec<_>>()));
}

#[test]
fn window_append() {
    let mut w = Window::with_capacity(9, 0);

    let v = (0..8).into_iter().collect::<Vec<_>>();
    w.append(0, v.as_slice()).unwrap();

    let v = (12..14).into_iter().collect::<Vec<_>>();
    w.append(12, v.as_slice()).unwrap();

    let v = (8..12).into_iter().collect::<Vec<_>>();
    w.append(8, v.as_slice()).unwrap();

    let v = (15..16).into_iter().collect::<Vec<_>>();
    w.append(15, v.as_slice()).unwrap();

    assert_eq!(w.to_string(), "[8, 9, 10, 11, 12, 13, <6, <15>>]");
}

#[test]
fn window_append_overflow() {
    let mut w = Window::with_capacity(9, 0);

    let v = (6..8).into_iter().collect::<Vec<_>>();
    w.append(6, v.as_slice()).unwrap();

    let v = (0..5).into_iter().collect::<Vec<_>>();
    w.append(0, v.as_slice()).unwrap();

    let v = (8..10).into_iter().collect::<Vec<_>>();
    w.append(8, v.as_slice()).unwrap();

    let v = (10..14).into_iter().collect::<Vec<_>>();
    w.append(10, v.as_slice()).unwrap();

    assert_eq!(w.to_string(), "[9, 10, 11, 12, 13>>, <0, <6, 7, 8]");
}

#[test]
fn window_append_overflow_overlapped() {
    let mut w = Window::with_capacity(9, 0);

    let v = (6..8).into_iter().collect::<Vec<_>>();
    w.append(6, v.as_slice()).unwrap();

    let v = (0..5).into_iter().collect::<Vec<_>>();
    w.append(0, v.as_slice()).unwrap();

    let v = (8..11).into_iter().collect::<Vec<_>>();
    w.append(8, v.as_slice()).unwrap();

    let v = (11..14).into_iter().collect::<Vec<_>>();
    w.append(11, v.as_slice()).unwrap();

    assert_eq!(w.to_string(), "[9, 10, 11, 12, 13>>, <0, <6, 7, 8]");
}

#[test]
fn window_append_overflow_overlapped_2() {
    let mut w = Window::with_capacity(9, 0);

    let v = (7..8).into_iter().collect::<Vec<_>>();
    w.append(7, v.as_slice()).unwrap();

    let v = (0..6).into_iter().collect::<Vec<_>>();
    w.append(0, v.as_slice()).unwrap();

    let v = (8..14).into_iter().collect::<Vec<_>>();
    w.append(8, v.as_slice()).unwrap();

    let v = (14..15).into_iter().collect::<Vec<_>>();
    w.append(14, v.as_slice()).unwrap();

    assert_eq!(w.to_string(), "[9, 10, 11, 12, 13, 14>>, <0, <7, 8]");
}

#[test]
fn window_append_prev_and_next() {
    let mut w = Window::with_capacity(8, 0);

    let v = (4..6).into_iter().collect::<Vec<_>>();
    w.append(4, v.as_slice()).unwrap();

    let v = (0..2).into_iter().collect::<Vec<_>>();
    w.append(0, v.as_slice()).unwrap();

    let v = (0..3).into_iter().collect::<Vec<_>>();
    let r = w.append(0, v.as_slice()).unwrap().unwrap();
    assert_eq!(r.len(), 1);

    let v = (252..254).into_iter().collect::<Vec<_>>();
    w.append(u32::MAX - 4, v.as_slice()).unwrap();

    let v = (11..13).into_iter().collect::<Vec<_>>();
    w.append(1, v.as_slice()).unwrap();

    assert_eq!(w.to_string(), "[0, 1, 2, <0, <4, 5>>]");
}
