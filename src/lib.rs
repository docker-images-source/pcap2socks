#![recursion_limit = "256"]

//! Redirect traffic to a SOCKS proxy with pcap.

use ipnetwork::Ipv4Network;
use log::{debug, info, trace, warn};
use lru::LruCache;
use rand::{self, Rng};
use stat::Traffic;
use std::cmp::{max, min};
use std::collections::{HashMap, VecDeque};
use std::net::{Ipv4Addr, Shutdown, SocketAddrV4};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};
use tokio::io;
use tokio::sync::mpsc;

pub mod packet;
pub mod pcap;
pub mod proxy;
pub mod stat;
pub mod tcp;

pub use self::proxy::ProxyConfig;
use self::proxy::{DatagramWorker, ForwardDatagram, ForwardStream, StreamWorker, TcpTimeout};
use packet::layer::arp::Arp;
use packet::layer::ethernet::Ethernet;
use packet::layer::icmpv4::Icmpv4;
use packet::layer::ipv4::Ipv4;
use packet::layer::tcp::Tcp;
use packet::layer::udp::Udp;
use packet::layer::{Layer, LayerKinds, Layers};
use packet::{Defraggler, Indicator};
use pcap::Interface;
use pcap::{HardwareAddr, Receiver, Sender};
use tcp::{CacheBudget, TcpRxState, TcpTxState};

/// Gets a list of available network interfaces for the current machine.
pub fn interfaces() -> Vec<Interface> {
    pcap::interfaces()
        .into_iter()
        .filter(|inter| inter.is_up() && !inter.is_loopback())
        .collect()
}

/// Gets an available network interface.
pub fn interface(name: Option<String>) -> Option<Interface> {
    let mut inters = match name {
        Some(ref name) => {
            let mut inters = interfaces();
            inters.retain(|inter| inter.name() == name);

            inters
        }
        None => interfaces(),
    };

    if inters.len() != 1 {
        None
    } else {
        Some(inters.pop().unwrap())
    }
}

/// Represents the max distance of `u32` values between packets in an `u32` window.
const MAX_U32_WINDOW_SIZE: usize = 16 * 1024 * 1024;

/// Represents the wait time after a `TimedOut` `IoError`.
const TIMEDOUT_WAIT: u64 = 20;

/// Represents if the receive-side silly window syndrome avoidance, Clark's algorithm, is enabled.
const ENABLE_RECV_SWS_AVOID: bool = true;
/// Represents if the send-side silly window syndrome avoidance, Clark's algorithm, is enabled.
const ENABLE_SEND_SWS_AVOID: bool = true;

/// Represents if the delayed ACK is enabled.
const ENABLE_DELAYED_ACK: bool = true;

/// Represents if the TCP MSS option is enabled.
const ENABLE_MSS: bool = true;

/// Represents the minimum frame size.
/// Because all traffic is in Ethernet, and the 802.3 specifies the minimum is 64 Bytes.
/// Exclude the 4 bytes used in FCS, the minimum frame size in pcap2socks is 60 Bytes.
const MINIMUM_FRAME_SIZE: usize = 60;

/// Represents a channel forward traffic to the source in pcap.
pub struct Forwarder {
    tx: Sender,
    src_mtu_map: HashMap<Ipv4Addr, usize>,
    local_mtu: usize,
    src_hardware_addr_map: HashMap<Ipv4Addr, HardwareAddr>,
    local_hardware_addr: HardwareAddr,
    local_ip_addr: Ipv4Addr,
    ipv4_identification_map: HashMap<(Ipv4Addr, Ipv4Addr), u16>,
    states: HashMap<(SocketAddrV4, SocketAddrV4), TcpTxState>,
    traffic_size: Option<Arc<AtomicUsize>>,
    traffic_count: Option<Arc<AtomicUsize>>,
}

#[allow(clippy::unnecessary_lazy_evaluations)]
impl Forwarder {
    /// Creates a new `Forwarder`.
    pub fn new(
        tx: Sender,
        mtu: usize,
        local_hardware_addr: HardwareAddr,
        local_ip_addr: Ipv4Addr,
    ) -> Forwarder {
        Forwarder::new_monitored(tx, mtu, local_hardware_addr, local_ip_addr, None)
    }

    /// Creates a new `Forwarder` which is monitored.
    pub fn new_monitored(
        tx: Sender,
        mtu: usize,
        local_hardware_addr: HardwareAddr,
        local_ip_addr: Ipv4Addr,
        traffic: Option<Traffic>,
    ) -> Forwarder {
        let size = traffic.as_ref().map(|traffic| traffic.size());
        let count = traffic.as_ref().map(|traffic| traffic.count());
        Forwarder {
            tx,
            src_mtu_map: HashMap::new(),
            local_mtu: mtu,
            src_hardware_addr_map: HashMap::new(),
            local_hardware_addr,
            local_ip_addr,
            ipv4_identification_map: HashMap::new(),
            states: HashMap::new(),
            traffic_size: size,
            traffic_count: count,
        }
    }

    /// Sets the source MTU.
    pub fn set_src_mtu(&mut self, src_ip_addr: Ipv4Addr, mtu: usize) -> bool {
        if !(68..=u16::MAX as usize).contains(&mtu) {
            return false;
        }
        let prev_mtu = *self
            .src_mtu_map
            .get(&src_ip_addr)
            .unwrap_or(&self.local_mtu);

        self.src_mtu_map
            .insert(src_ip_addr, min(self.local_mtu, mtu));
        trace!("set source MTU of {} to {}", src_ip_addr, mtu);

        return *self
            .src_mtu_map
            .get(&src_ip_addr)
            .unwrap_or(&self.local_mtu)
            != prev_mtu;
    }

    /// Sets the source hardware address.
    pub fn set_src_hardware_addr(&mut self, src_ip_addr: Ipv4Addr, hardware_addr: HardwareAddr) -> bool {
        if self.src_hardware_addr_map.get(&src_ip_addr) == Some(&hardware_addr) {
            return false;
        }
        self.src_hardware_addr_map.insert(src_ip_addr, hardware_addr);
        trace!("set source hardware address of {} to {}", src_ip_addr, hardware_addr);
        true
    }

    /// Sets the local IP address.
    pub fn set_local_ip_addr(&mut self, ip_addr: Ipv4Addr) {
        self.local_ip_addr = ip_addr;
        trace!("set local IP address to {}", ip_addr);
    }

    fn increase_ipv4_identification(&mut self, dst_ip_addr: Ipv4Addr, src_ip_addr: Ipv4Addr) {
        let entry = self
            .ipv4_identification_map
            .entry((src_ip_addr, dst_ip_addr))
            .or_insert(0);
        *entry = entry.wrapping_add(1);
        trace!(
            "increase IPv4 identification of {} -> {} to {}",
            dst_ip_addr,
            src_ip_addr,
            entry
        );
    }

    /// Sets the state of a TCP connection.
    pub fn set_state(&mut self, dst: SocketAddrV4, src: SocketAddrV4, state: TcpTxState) {
        let key = (src, dst);

        self.states.insert(key, state);
    }

    /// Removes all information related to a TCP connection.
    pub fn clean_up(&mut self, dst: SocketAddrV4, src: SocketAddrV4) {
        let key = (src, dst);

        self.states.remove(&key);
    }

    /// Returns the source MTU.
    pub fn get_src_mtu(&self, src_ip_addr: Ipv4Addr) -> usize {
        *self
            .src_mtu_map
            .get(&src_ip_addr)
            .unwrap_or(&self.local_mtu)
    }

    /// Returns the state of a TCP connection.
    pub fn get_state(&self, dst: SocketAddrV4, src: SocketAddrV4) -> Option<&TcpTxState> {
        let key = (src, dst);

        self.states.get(&key)
    }

    /// Returns the mutable state of a TCP connection.
    pub fn get_state_mut(
        &mut self,
        dst: SocketAddrV4,
        src: SocketAddrV4,
    ) -> Option<&mut TcpTxState> {
        let key = (src, dst);

        self.states.get_mut(&key)
    }

    fn get_tcp_window(&self, dst: SocketAddrV4, src: SocketAddrV4) -> u16 {
        let key = (src, dst);

        let state = self.states.get(&key).unwrap();

        // Avoid SWS
        if ENABLE_RECV_SWS_AVOID {
            let thresh = min(state.half_max_window() as usize, self.local_mtu);

            if (state.window() as usize) < thresh {
                0
            } else {
                state.window()
            }
        } else {
            state.window()
        }
    }

    /// Returns the size of the cache and the queue of a TCP connection.
    pub fn get_cache_size(&mut self, dst: SocketAddrV4, src: SocketAddrV4) -> usize {
        let key = (src, dst);

        let state = self.states.get(&key).unwrap();

        state.cache().len() + state.queue().len()
    }

    /// Sends an ARP reply packet.
    pub fn send_arp_reply(&mut self, src_ip_addr: Ipv4Addr) -> io::Result<()> {
        // ARP
        let arp = Arp::new_reply(
            self.local_hardware_addr,
            self.local_ip_addr,
            *self
                .src_hardware_addr_map
                .get(&src_ip_addr)
                .unwrap_or(&pcap::HARDWARE_ADDR_UNSPECIFIED),
            src_ip_addr,
        );

        // Send
        self.send_ethernet(arp.dst_hardware_addr(), Layers::Arp(arp), None, None)
    }

    /// Sends an gratuitous ARP packet.
    pub fn send_gratuitous_arp(&mut self) -> io::Result<()> {
        // ARP
        let arp = Arp::gratuitous_arp(self.local_hardware_addr, self.local_ip_addr);

        // Send
        self.send_ethernet(pcap::HARDWARE_ADDR_BROADCAST, Layers::Arp(arp), None, None)
    }

    /// Sends an ICMPv4 echo reply packet.
    pub fn send_icmpv4_echo_reply(
        &mut self,
        dst_ip_addr: Ipv4Addr,
        src_ip_addr: Ipv4Addr,
        identifier: u16,
        sequence_number: u16,
    ) -> io::Result<()> {
        // ICMPv4
        let icmpv4 = Icmpv4::new_echo_reply(identifier, sequence_number);

        self.send_ipv4(dst_ip_addr, src_ip_addr, Layers::Icmpv4(icmpv4), None)
    }

    /// Sends an ICMPv4 destination host unreachable packet.
    pub fn send_icmpv4_destination_host_unreachable(
        &mut self,
        dst_ip_addr: Ipv4Addr,
        src_ip_addr: Ipv4Addr,
        payload: &[u8],
    ) -> io::Result<()> {
        // ICMPv4
        let icmpv4 = Icmpv4::new_destination_host_unreachable(payload);

        self.send_ipv4(dst_ip_addr, src_ip_addr, Layers::Icmpv4(icmpv4), None)
    }

    /// Sends an ICMPv4 destination port unreachable packet.
    pub fn send_icmpv4_destination_port_unreachable(
        &mut self,
        dst_ip_addr: Ipv4Addr,
        src_ip_addr: Ipv4Addr,
        payload: &[u8],
    ) -> io::Result<()> {
        // ICMPv4
        let icmpv4 = Icmpv4::new_destination_port_unreachable(payload);

        self.send_ipv4(dst_ip_addr, src_ip_addr, Layers::Icmpv4(icmpv4), None)
    }

    /// Appends TCP payload to the queue.
    pub fn queue_tcp(
        &mut self,
        dst: SocketAddrV4,
        src: SocketAddrV4,
        payload: &[u8],
    ) -> io::Result<()> {
        // Append to queue
        let state = self
            .get_state_mut(dst, src)
            .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
        state.append_queue(payload)?;

        self.send_tcp(dst, src)
    }

    /// Retransmits TCP packets from the cache. This method is used for fast retransmission.
    pub fn retransmit_tcp(
        &mut self,
        dst: SocketAddrV4,
        src: SocketAddrV4,
        sacks: Option<Vec<(u32, u32)>>,
    ) -> io::Result<()> {
        let state = self
            .get_state_mut(dst, src)
            .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
        let sequence = state.cache().sequence();
        let recv_next = state.cache().recv_next();

        // Congestion control
        if let Some(cc) = &mut state.cc_mut() {
            cc.fast_retransmission();
        }

        // Find all disjointed ranges
        let mut ranges = vec![(sequence, recv_next), ];
        if let Some(sacks) = sacks {
            for sack in sacks {
                let mut temp_ranges = Vec::new();

                for range in ranges {
                    for temp_range in disjoint_u32_range(range, sack) {
                        temp_ranges.push(temp_range);
                    }
                }

                ranges = temp_ranges;
            }
        }
        let ranges = ranges;

        // Retransmit
        for range in &ranges {
            let size = range.1.wrapping_sub(range.0) as usize;
            let state = self
                .get_state(dst, src)
                .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
            let payload = state.cache().get(range.0, size)?;
            if !payload.is_empty() {
                if range.1 == recv_next && state.cache_fin().is_some() {
                    // ACK/FIN
                    trace!(
                        "retransmit TCP ACK/FIN ({} Bytes) {} -> {} from {}",
                        payload.len(),
                        dst,
                        src,
                        sequence
                    );

                    // Send
                    self.send_tcp_ack(dst, src, range.0, payload.as_slice(), true)?;
                } else {
                    // ACK
                    trace!(
                        "retransmit TCP ACK ({} Bytes) {} -> {} from {}",
                        payload.len(),
                        dst,
                        src,
                        sequence
                    );

                    // Send
                    self.send_tcp_ack(dst, src, range.0, payload.as_slice(), false)?;
                }
            }
        }

        // Pure FIN
        let state = self
            .get_state(dst, src)
            .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
        if ranges.is_empty() && state.cache_fin().is_some() {
            // FIN
            trace!("retransmit TCP FIN {} -> {}", dst, src);

            // Send
            self.send_tcp_fin(dst, src)?;
        }

        Ok(())
    }

    /// Retransmits timed out TCP packets from the cache. This method is used for transmitting
    /// timed out data.
    pub fn retransmit_tcp_timedout(
        &mut self,
        dst: SocketAddrV4,
        src: SocketAddrV4,
    ) -> io::Result<()> {
        let state = self
            .get_state_mut(dst, src)
            .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
        // SYN-ACK retransmissions must use the RTO timer, never incoming ACKs.
        if state.cache_syn().is_some() {
            if state.syn_retransmit_due() {
                state.double_rto();
                state.update_syn_timer();
                self.send_tcp_ack_syn(dst, src)?;
            }
            return Ok(());
        }
        let next_rto = state.next_rto();
        let payload = state.cache_mut().get_timed_out_and_update(next_rto);
        let sequence = state.cache().sequence();
        let size = state.cache().len();

        if size > 0 {
            if !payload.is_empty() {
                // Double RTO
                state.double_rto();

                // Congestion control
                if let Some(cc) = &mut state.cc_mut() {
                    cc.timedout();
                }

                // If all the cache is get, the FIN should also be sent
                if size == payload.len() && state.cache_fin().is_some() {
                    // ACK/FIN
                    state.update_fin_timer();
                    trace!(
                        "retransmit TCP ACK/FIN ({} Bytes) and FIN {} -> {} from {} due to timeout",
                        payload.len(),
                        dst,
                        src,
                        sequence
                    );

                    // Send
                    self.send_tcp_ack(dst, src, sequence, payload.as_slice(), true)?;
                } else {
                    // ACK
                    trace!(
                        "retransmit TCP ACK ({} Bytes) {} -> {} from {} due to timeout",
                        payload.len(),
                        dst,
                        src,
                        sequence
                    );

                    // Send
                    self.send_tcp_ack(dst, src, sequence, payload.as_slice(), false)?;
                }
            }
        } else {
            // FIN
            if let Some(timer) = state.cache_fin() {
                if timer.is_timedout() {
                    // Double RTO
                    state.double_rto();
                    state.update_fin_timer();
                    trace!("retransmit TCP FIN {} -> {} due to timeout", dst, src);

                    // Send
                    self.send_tcp_fin(dst, src)?;
                }
            }
        }

        // Delayed ACK0
        let state = self
            .get_state(dst, src)
            .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
        if state.delayed_ack() {
            self.send_tcp_ack_0(dst, src)?;
        }

        Ok(())
    }

    /// Sends TCP packets from the queue.
    pub fn send_tcp(&mut self, dst: SocketAddrV4, src: SocketAddrV4) -> io::Result<()> {
        // Retransmit outstanding SYN-ACK only from the periodic RTO timer.
        let state = self
            .get_state(dst, src)
            .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
        if state.cache_syn().is_some() {
            return Ok(());
        }

        if state.src_window() > 0 {
            // TCP sequence
            let sent_size = state.cache().len();
            let remain_size = state.send_window().saturating_sub(sent_size);
            // The peer's scaled window may exceed our bounded retransmission cache.
            let remain_size = min(remain_size, state.cache().remaining());
            let remain_size = min(remain_size, u16::MAX as usize) as u16;

            let mut size = min(remain_size as usize, state.queue().len());
            // Avoid SWS
            if ENABLE_SEND_SWS_AVOID {
                let mtu = *self.src_mtu_map.get(src.ip()).unwrap_or(&self.local_mtu);
                let mss = mtu - (Ipv4::minimum_len() + Tcp::minimum_len());

                if size < mss && !state.cache().is_empty() {
                    size = 0;
                }
            }
            let size = size;
            if size > 0 {
                let state = self
                    .get_state_mut(dst, src)
                    .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
                let payload = state.append_cache(size)?;

                // If the queue is empty and a FIN is in the queue, pop it
                if state.queue().is_empty() && state.queue_fin() {
                    // ACK/FIN
                    state.append_cache_fin();

                    // Send
                    let state = self
                        .get_state(dst, src)
                        .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
                    let sequence = state.sequence();
                    self.send_tcp_ack(dst, src, sequence, &payload, true)?;
                } else {
                    // ACK
                    let state = self
                        .get_state(dst, src)
                        .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
                    let sequence = state.sequence();
                    self.send_tcp_ack(dst, src, sequence, &payload, false)?;
                }
            }
        }

        // If the queue is empty and a FIN is in the queue, pop it
        // FIN
        let state = self
            .get_state_mut(dst, src)
            .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
        #[allow(clippy::collapsible_if)]
        if state.queue_fin() {
            if state.cache().is_empty() {
                // FIN
                state.append_cache_fin();

                // Send
                self.send_tcp_fin(dst, src)?;
            }
        }

        Ok(())
    }

    fn fin_for_segment(is_fin: bool, end: usize, total: usize) -> bool {
        is_fin && end == total
    }

    fn send_tcp_ack(
        &mut self,
        dst: SocketAddrV4,
        src: SocketAddrV4,
        sequence: u32,
        payload: &[u8],
        is_fin: bool,
    ) -> io::Result<()> {
        // Segmentation
        let mss = *self.src_mtu_map.get(src.ip()).unwrap_or(&self.local_mtu)
            - (Ipv4::minimum_len() + Tcp::minimum_len());
        let payload_len = payload.len();
        let mut i = 0;
        while mss * i < payload_len {
            let state = self
                .get_state(dst, src)
                .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
            let size = min(mss, payload.len() - i * mss);
            let payload = &payload[i * mss..i * mss + size];
            let sequence = sequence.wrapping_add((i * mss) as u32);
            let mut recv_next = sequence.wrapping_add(size as u32);

            // TCP
            let tcp;
            if Self::fin_for_segment(is_fin, i * mss + size, payload_len) {
                // ACK/FIN
                tcp = Tcp::new_ack_fin(
                    dst.port(),
                    src.port(),
                    sequence,
                    state.acknowledgement(),
                    self.get_tcp_window(dst, src),
                    None,
                );
                recv_next = recv_next.checked_add(1).unwrap_or(0);
            } else {
                // ACK
                tcp = Tcp::new_ack(
                    dst.port(),
                    src.port(),
                    sequence,
                    state.acknowledgement(),
                    self.get_tcp_window(dst, src),
                    None,
                    None,
                );
            }

            // Send
            self.send_ipv4(
                *dst.ip(),
                *src.ip(),
                Layers::Tcp(tcp),
                Some(payload),
            )?;

            // Clear TCP delayed ACK
            let state = self
                .get_state_mut(dst, src)
                .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
            state.clear_delayed_ack();

            // Update TCP sequence
            let record_sequence = state.sequence();
            let sub_sequence = recv_next.wrapping_sub(record_sequence);
            if (sub_sequence as usize) <= MAX_U32_WINDOW_SIZE {
                state.add_sequence(sub_sequence);
            }

            i += 1;
        }

        Ok(())
    }

    /// Sends an TCP delayed ACK packet without payload.
    pub fn send_tcp_delay_ack_0(&mut self, dst: SocketAddrV4, src: SocketAddrV4) -> io::Result<()> {
        if ENABLE_DELAYED_ACK {
            let state = self
                .get_state_mut(dst, src)
                .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;

            if state.delayed_ack() {
                self.send_tcp_ack_0(dst, src)?;
            } else {
                state.set_delayed_ack();
            }
        } else {
            self.send_tcp_ack_0(dst, src)?;
        }

        Ok(())
    }

    /// Sends an TCP ACK packet without payload.
    pub fn send_tcp_ack_0(&mut self, dst: SocketAddrV4, src: SocketAddrV4) -> io::Result<()> {
        // TCP
        let state = self
            .get_state(dst, src)
            .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
        let tcp = Tcp::new_ack(
            dst.port(),
            src.port(),
            state.sequence(),
            state.acknowledgement(),
            self.get_tcp_window(dst, src),
            state.sacks().clone(),
            None,
        );

        // Send
        self.send_ipv4(*dst.ip(), *src.ip(), Layers::Tcp(tcp), None)?;

        // Clear TCP delayed ACK
        let state = self
            .get_state_mut(dst, src)
            .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
        state.clear_delayed_ack();

        Ok(())
    }

    fn send_tcp_ack_syn(&mut self, dst: SocketAddrV4, src: SocketAddrV4) -> io::Result<()> {
        let mss = match ENABLE_MSS {
            true => {
                let mss = self.local_mtu - (Ipv4::minimum_len() + Tcp::minimum_len());
                let mss = if mss > u16::MAX as usize {
                    u16::MAX
                } else {
                    mss as u16
                };

                Some(mss)
            }
            false => None,
        };

        // TCP
        let state = self
            .get_state(dst, src)
            .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
        let tcp = Tcp::new_ack_syn(
            dst.port(),
            src.port(),
            state.sequence(),
            state.acknowledgement(),
            self.get_tcp_window(dst, src),
            mss,
            state.src_wscale(),
            state.sack_perm(),
            None,
        );

        // Send
        self.send_ipv4(*dst.ip(), *src.ip(), Layers::Tcp(tcp), None)?;

        // Clear TCP delayed ACK
        let state = self
            .get_state_mut(dst, src)
            .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
        state.clear_delayed_ack();

        Ok(())
    }

    /// Sends an TCP ACK/RST packet.
    pub fn send_tcp_ack_rst(&mut self, dst: SocketAddrV4, src: SocketAddrV4) -> io::Result<()> {
        // TCP
        let state = self
            .get_state(dst, src)
            .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
        let tcp = Tcp::new_ack_rst(
            dst.port(),
            src.port(),
            state.sequence(),
            state.acknowledgement(),
            self.get_tcp_window(dst, src),
            None,
        );

        // Send
        self.send_ipv4(*dst.ip(), *src.ip(), Layers::Tcp(tcp), None)?;

        // Clear TCP delayed ACK
        let state = self
            .get_state_mut(dst, src)
            .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
        state.clear_delayed_ack();

        Ok(())
    }

    /// Sends an TCP ACK/RST packet of an untracked connection.
    pub fn send_tcp_ack_rst_untracked(
        &mut self,
        dst: SocketAddrV4,
        src: SocketAddrV4,
        sequence: u32,
    ) -> io::Result<()> {
        // TCP
        let tcp = Tcp::new_ack_rst(dst.port(), src.port(), sequence, 0, 0, None);

        // Send
        self.send_ipv4(*dst.ip(), *src.ip(), Layers::Tcp(tcp), None)
    }

    /// Sends an TCP RST packet.
    pub fn send_tcp_rst(
        &mut self,
        dst: SocketAddrV4,
        src: SocketAddrV4,
        sequence: u32,
    ) -> io::Result<()> {
        // TCP
        let tcp = Tcp::new_rst(dst.port(), src.port(), sequence, 0, 0, None);

        // Send
        self.send_ipv4(*dst.ip(), *src.ip(), Layers::Tcp(tcp), None)
    }

    fn send_tcp_fin(&mut self, dst: SocketAddrV4, src: SocketAddrV4) -> io::Result<()> {
        // TCP
        let state = self
            .get_state(dst, src)
            .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
        let tcp = Tcp::new_fin(
            dst.port(),
            src.port(),
            state.sequence(),
            state.acknowledgement(),
            self.get_tcp_window(dst, src),
            None,
        );

        // Send
        self.send_ipv4(*dst.ip(), *src.ip(), Layers::Tcp(tcp), None)
    }

    /// Sends UDP packets.
    pub fn send_udp(
        &mut self,
        dst: SocketAddrV4,
        src: SocketAddrV4,
        payload: &[u8],
    ) -> io::Result<()> {
        // UDP
        let udp = Udp::new(dst.port(), src.port());

        self.send_ipv4(
            *dst.ip(),
            *src.ip(),
            Layers::Udp(udp),
            Some(payload),
        )
    }

    fn send_ipv4(
        &mut self,
        dst_ip_addr: Ipv4Addr,
        src_ip_addr: Ipv4Addr,
        mut transport: Layers,
        payload: Option<&[u8]>,
    ) -> io::Result<()> {
        // Fragmentation
        let size = transport.len()
            + match payload {
                Some(payload) => payload.len(),
                None => 0,
            };
        let mtu = *self
            .src_mtu_map
            .get(&src_ip_addr)
            .unwrap_or(&self.local_mtu);
        let mss = mtu.checked_sub(Ipv4::minimum_len())
            .filter(|&mss| mss >= 8)
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "invalid IPv4 MTU"))?;
        if size <= mss {
            // IPv4
            let ipv4 = Ipv4::new(
                *self
                    .ipv4_identification_map
                    .get(&(src_ip_addr, dst_ip_addr))
                    .unwrap_or(&0),
                transport.kind(),
                dst_ip_addr,
                src_ip_addr,
            )
            .unwrap();

            // Set IPv4 layer for checksum
            match transport {
                Layers::Tcp(ref mut tcp) => tcp.set_ipv4_layer(&ipv4),
                Layers::Udp(ref mut udp) => udp.set_ipv4_layer(&ipv4),
                _ => {}
            }

            // Send
            self.send_ethernet(
                *self
                    .src_hardware_addr_map
                    .get(&src_ip_addr)
                    .unwrap_or(&pcap::HARDWARE_ADDR_UNSPECIFIED),
                Layers::Ipv4(ipv4),
                Some(transport),
                payload,
            )?;
        } else {
            // Pseudo header
            let ipv4 = Ipv4::new(0, transport.kind(), dst_ip_addr, src_ip_addr).unwrap();

            // Set IPv4 layer for checksum
            match &mut transport {
                Layers::Tcp(tcp) => tcp.set_ipv4_layer(&ipv4),
                Layers::Udp(udp) => udp.set_ipv4_layer(&ipv4),
                _ => {}
            }

            // Payload
            let mut buffer = vec![0u8; size];
            match payload {
                Some(payload) => transport.serialize_with_payload(
                    buffer.as_mut_slice(),
                    payload,
                    transport.len() + payload.len(),
                )?,
                None => transport.serialize(buffer.as_mut_slice(), transport.len())?,
            };

            let mut n = 0;
            while n < size {
                let mut length = min(size - n, mss);
                let mut remain = size - n - length;
                if remain > 0 && length < 16 {
                    return Err(io::Error::new(io::ErrorKind::InvalidInput, "MTU too small for fragmentation"));
                }

                // Alignment
                if remain > 0 {
                    length = length / 8 * 8;
                    remain = size - n - length;
                }

                // Leave at least 8 Bytes for last fragment
                if remain > 0 && remain < 8 {
                    length -= 8;
                }
                if length == 0 {
                    return Err(io::Error::new(io::ErrorKind::InvalidInput, "zero-length IPv4 fragment"));
                }

                // IPv4
                let ipv4 = if remain > 0 {
                    Ipv4::new_more_fragment(
                        *self
                            .ipv4_identification_map
                            .get(&(src_ip_addr, dst_ip_addr))
                            .unwrap_or(&0),
                        transport.kind(),
                        (n / 8) as u16,
                        dst_ip_addr,
                        src_ip_addr,
                    )
                    .unwrap()
                } else {
                    Ipv4::new_last_fragment(
                        *self
                            .ipv4_identification_map
                            .get(&(src_ip_addr, dst_ip_addr))
                            .unwrap_or(&0),
                        transport.kind(),
                        (n / 8) as u16,
                        dst_ip_addr,
                        src_ip_addr,
                    )
                    .unwrap()
                };

                // Send
                self.send_ethernet(
                    *self
                        .src_hardware_addr_map
                        .get(&src_ip_addr)
                        .unwrap_or(&pcap::HARDWARE_ADDR_UNSPECIFIED),
                    Layers::Ipv4(ipv4),
                    None,
                    Some(&buffer[n..n + length]),
                )?;

                n += length;
            }
        }

        // Update IPv4 identification
        self.increase_ipv4_identification(dst_ip_addr, src_ip_addr);

        Ok(())
    }

    fn send_ethernet(
        &mut self,
        src_hardware_addr: HardwareAddr,
        network: Layers,
        transport: Option<Layers>,
        payload: Option<&[u8]>,
    ) -> io::Result<()> {
        // Ethernet
        let ethernet =
            Ethernet::new(network.kind(), self.local_hardware_addr, src_hardware_addr).unwrap();

        // Indicator
        let indicator = Indicator::new(Layers::Ethernet(ethernet), Some(network), transport);

        // Send
        match payload {
            Some(payload) => self.send_with_payload(&indicator, payload),
            None => self.send(&indicator),
        }
    }

    fn send(&mut self, indicator: &Indicator) -> io::Result<()> {
        // Serialize and send
        let size = indicator.len();
        let buffer_size = max(size, MINIMUM_FRAME_SIZE);
        let mut result = None;
        self.tx.build_and_send(1, buffer_size, &mut |buffer| {
            if let Err(e) = indicator.serialize(&mut buffer[..size]) {
                result = Some(e);
            }
        })
        .ok_or_else(|| io::Error::new(io::ErrorKind::WouldBlock, "pcap transmit buffer unavailable"))??;
        match result {
            Some(e) => return Err(e),
            None => trace!("send to pcap: {} ({} Bytes)", indicator.brief(), size),
        }

        // Monitor
        if let Some(size) = &self.traffic_size {
            size.fetch_add(buffer_size, Ordering::Relaxed);
        }
        if let Some(count) = &self.traffic_count {
            count.fetch_add(1, Ordering::Relaxed);
        }

        Ok(())
    }

    fn send_with_payload(&mut self, indicator: &Indicator, payload: &[u8]) -> io::Result<()> {
        // Serialize and send
        let size = indicator.len();
        let buffer_size = max(size + payload.len(), MINIMUM_FRAME_SIZE);
        let mut result = None;
        self.tx
            .build_and_send(1, buffer_size, &mut |buffer| {
                if let Err(e) =
                    indicator.serialize_with_payload(&mut buffer[..size + payload.len()], payload)
                {
                    result = Some(e);
                }
            })
            .ok_or_else(|| io::Error::new(io::ErrorKind::WouldBlock, "pcap transmit buffer unavailable"))??;
        match result {
            Some(e) => return Err(e),
            None => trace!(
                "send to pcap: {} ({} + {} Bytes)",
                indicator.brief(),
                size,
                payload.len()
            ),
        }

        // Monitor
        if let Some(size) = &self.traffic_size {
            size.fetch_add(buffer_size, Ordering::Relaxed);
        }
        if let Some(count) = &self.traffic_count {
            count.fetch_add(1, Ordering::Relaxed);
        }

        Ok(())
    }
}

impl ForwardStream for Forwarder {
    fn open(&mut self, dst: SocketAddrV4, src: SocketAddrV4) -> io::Result<()> {
        self.send_tcp_ack_syn(dst, src)?;

        let state = self
            .get_state_mut(dst, src)
            .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
        state.update_syn_timer();

        Ok(())
    }

    fn forward(&mut self, dst: SocketAddrV4, src: SocketAddrV4, payload: &[u8]) -> io::Result<()> {
        let state = self
            .get_state(dst, src)
            .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
        if state.cache_fin().is_some() || state.queue_fin() {
            return Err(io::Error::from(io::ErrorKind::InvalidData));
        }

        self.queue_tcp(dst, src, payload)
    }

    fn tick(&mut self, dst: SocketAddrV4, src: SocketAddrV4) -> io::Result<()> {
        let state = self
            .get_state(dst, src)
            .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
        if state.is_stalled() {
            return Err(io::Error::new(
                io::ErrorKind::TimedOut,
                "TCP acknowledgement stalled",
            ));
        }
        self.retransmit_tcp_timedout(dst, src)
    }

    fn close(&mut self, dst: SocketAddrV4, src: SocketAddrV4) -> io::Result<()> {
        let state = match self.get_state_mut(dst, src) {
            Some(state) => state,
            None => return Ok(()),
        };
        state.append_queue_fin();

        self.send_tcp(dst, src)
    }

    fn check(&self, dst: SocketAddrV4, src: SocketAddrV4) -> io::Result<usize> {
        let state = self
            .get_state(dst, src)
            .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
        Ok(state.queue_remaining())
    }
}

impl ForwardDatagram for Forwarder {
    fn forward(&mut self, dst: SocketAddrV4, src: SocketAddrV4, payload: &[u8]) -> io::Result<()> {
        self.send_udp(dst, src, payload)
    }
}

#[allow(clippy::unnecessary_lazy_evaluations)]
fn disjoint_u32_range(main: (u32, u32), sub: (u32, u32)) -> Vec<(u32, u32)> {
    let size_main = main.1.wrapping_sub(main.0) as usize;
    let diff_first = sub.0.wrapping_sub(main.0) as usize;
    let diff_second = sub.1.wrapping_sub(main.1) as usize;
    let mut vector = Vec::with_capacity(2);

    #[allow(clippy::collapsible_if)]
    if diff_first <= MAX_U32_WINDOW_SIZE {
        if diff_second > MAX_U32_WINDOW_SIZE {
            // sub is in the main
            vector.push((main.0, sub.0));
            vector.push((sub.1, main.1));
        } else {
            #[allow(clippy::collapsible_if)]
            if diff_first >= size_main {
                // sub is in the right of the main
                vector.push((main.0, main.1));
            } else {
                // sub overlaps the right part of the main
                vector.push((main.0, sub.0));
            }
        }
    } else {
        #[allow(clippy::collapsible_if)]
        if diff_second > MAX_U32_WINDOW_SIZE {
            // The distance between the main's left edge and the sub's right edge
            let diff = sub.1.wrapping_sub(main.0) as usize;
            if diff > MAX_U32_WINDOW_SIZE {
                // sub is in the left of the main
                vector.push((main.0, main.1));
            } else {
                // sub overlaps the left part of the main
                vector.push((sub.1, main.1));
            }
        } else {
            // sub covers the main
        }
    }

    vector
}

/// Represents the threshold of TCP ACK duplicates before trigger a fast retransmission.
const DUPLICATES_THRESHOLD: usize = 3;
/// Represents the cool down time between 2 retransmissions.
const RETRANS_COOL_DOWN: u128 = 200;

/// Represents if the TCP selective acknowledgment option is enabled.
const ENABLE_SACK: bool = true;

/// Represents if the TCP window scale option is enabled.
const ENABLE_WSCALE: bool = true;
/// Represents the max window scale of the receive window.
const MAX_RECV_WSCALE: u8 = 8;

/// Represents the max limit of UDP port for binding in local.
const MAX_UDP_PORT: usize = 256;
/// Retire idle UDP mappings instead of stealing a still-active association.
const UDP_IDLE_TIMEOUT: Duration = Duration::from_secs(2 * 60 * 60);
/// At capacity, reclaim only long-inactive associations, never recent ones.
const UDP_PRESSURE_IDLE_TIMEOUT: Duration = Duration::from_secs(10 * 60);
/// Represents the interval for reclaiming closed UDP associations.
const UDP_CLEANUP_INTERVAL: Duration = Duration::from_secs(30);
/// Drop TCP sessions that have received no client traffic for two hours.
const TCP_IDLE_TIMEOUT: Duration = Duration::from_secs(2 * 60 * 60);
/// Avoid unbounded TCP stream and related cache proliferation.
const MAX_TCP_STREAMS: usize = 256;
/// Shared limit on the actual growable TCP receive-window byte buffers.
const MAX_GLOBAL_TCP_RX_CACHE_BYTES: usize = 64 * 1024 * 1024;
/// Shared bound on outstanding TCP payload in outbound queues and caches.
const MAX_GLOBAL_TCP_TX_CACHE_BYTES: usize = 64 * 1024 * 1024;
/// Bound proxy handshakes and buffered initial UDP datagrams.
const MAX_PENDING_TCP_CONNECTS: usize = 64;
const MAX_PENDING_UDP_ASSOCIATIONS: usize = 64;
const MAX_PENDING_UDP_DATAGRAMS: usize = 32;
/// Longer than the SOCKS connect and associate timeouts combined.
const UDP_ASSOCIATE_DEADLINE: Duration = Duration::from_secs(20);

struct PendingUdpAssociation {
    id: u64,
    started: Instant,
    task: tokio::task::JoinHandle<()>,
    datagrams: VecDeque<(Vec<u8>, SocketAddrV4)>,
}

type TcpReady = (SocketAddrV4, SocketAddrV4, u64, io::Result<tokio::net::TcpStream>);
type UdpReady = (SocketAddrV4, u64, io::Result<(DatagramWorker, u16)>);

/// Represents a channel redirect traffic to the proxy or loopback to the source in pcap.
pub struct Redirector {
    tx: Arc<Mutex<Forwarder>>,
    src_ip_addr: Ipv4Network,
    local_ip_addr: Ipv4Addr,
    interface_ip_addr: Ipv4Addr,
    interface_hardware_addr: HardwareAddr,
    gw_ip_addr: Option<Ipv4Addr>,
    proxy: ProxyConfig,
    streams: HashMap<(SocketAddrV4, SocketAddrV4), StreamWorker>,
    states: HashMap<(SocketAddrV4, SocketAddrV4), TcpRxState>,
    stream_ids: HashMap<(SocketAddrV4, SocketAddrV4), u64>,
    next_stream_id: u64,
    tcp_timeout_tx: mpsc::UnboundedSender<TcpTimeout>,
    tcp_timeout_rx: mpsc::UnboundedReceiver<TcpTimeout>,
    tcp_ready_tx: mpsc::UnboundedSender<TcpReady>,
    tcp_ready_rx: mpsc::UnboundedReceiver<TcpReady>,
    pending_tcp: HashMap<(SocketAddrV4, SocketAddrV4), (u64, tokio::task::JoinHandle<()>)>,
    tcp_queued_bytes: Arc<AtomicUsize>,
    tcp_rx_cache_budget: Arc<CacheBudget>,
    tcp_tx_cache_budget: Arc<CacheBudget>,
    udp_ready_tx: mpsc::UnboundedSender<UdpReady>,
    udp_ready_rx: mpsc::UnboundedReceiver<UdpReady>,
    pending_udp: HashMap<SocketAddrV4, PendingUdpAssociation>,
    next_udp_id: u64,
    datagrams: HashMap<u16, DatagramWorker>,
    /// Represents the map mapping a source port to a local port.
    datagram_map: HashMap<SocketAddrV4, u16>,
    /// Represents the LRU mapping a local port to a source port.
    udp_lru: LruCache<u16, SocketAddrV4>,
    defrag: Defraggler,
    traffic_size: Option<Arc<AtomicUsize>>,
    traffic_count: Option<Arc<AtomicUsize>>,
}

impl Redirector {
    /// Creates a new `Redirector`.
    pub fn new(
        tx: Arc<Mutex<Forwarder>>,
        src_ip_addr: Ipv4Network,
        local_ip_addr: Ipv4Addr,
        gw_ip_addr: Option<Ipv4Addr>,
        proxy: ProxyConfig,
        traffic: Option<Traffic>,
    ) -> Redirector {
        let size = traffic.as_ref().map(|traffic| traffic.size());
        let count = traffic.as_ref().map(|traffic| traffic.count());
        // Snapshot the interface addresses before the virtual gateway overrides its IP.
        let (interface_ip_addr, interface_hardware_addr) = {
            let forwarder = tx.lock().unwrap();
            (forwarder.local_ip_addr, forwarder.local_hardware_addr)
        };
        let (tcp_timeout_tx, tcp_timeout_rx) = mpsc::unbounded_channel();
        let (tcp_ready_tx, tcp_ready_rx) = mpsc::unbounded_channel();
        let (udp_ready_tx, udp_ready_rx) = mpsc::unbounded_channel();
        let redirector = Redirector {
            tx,
            src_ip_addr,
            local_ip_addr,
            interface_ip_addr,
            interface_hardware_addr,
            gw_ip_addr,
            proxy,
            streams: HashMap::new(),
            states: HashMap::new(),
            stream_ids: HashMap::new(),
            next_stream_id: 0,
            tcp_timeout_tx,
            tcp_timeout_rx,
            tcp_ready_tx,
            tcp_ready_rx,
            pending_tcp: HashMap::new(),
            tcp_queued_bytes: Arc::new(AtomicUsize::new(0)),
            tcp_rx_cache_budget: Arc::new(CacheBudget::new(MAX_GLOBAL_TCP_RX_CACHE_BYTES)),
            tcp_tx_cache_budget: Arc::new(CacheBudget::new(MAX_GLOBAL_TCP_TX_CACHE_BYTES)),
            udp_ready_tx,
            udp_ready_rx,
            pending_udp: HashMap::new(),
            next_udp_id: 0,
            datagrams: HashMap::new(),
            datagram_map: HashMap::new(),
            udp_lru: LruCache::new(MAX_UDP_PORT),
            defrag: Defraggler::new(),
            traffic_size: size,
            traffic_count: count,
        };
        if let Some(gw_ip_addr) = gw_ip_addr {
            redirector.tx.lock().unwrap().set_local_ip_addr(gw_ip_addr);
        }

        redirector
    }

    /// Let the host TCP/IP stack handle services bound to its actual address.
    /// Do not bypass a remote WireGuard subnet: those destinations still proxy.
    fn should_proxy_ipv4(&self, src: Ipv4Addr, dst: Ipv4Addr) -> bool {
        src != self.local_ip_addr
            && self.src_ip_addr.contains(src)
            && dst != self.interface_ip_addr
    }

    /// Opens an `Interface` for redirection.
    pub async fn open(&mut self, rx: &mut Receiver) -> io::Result<()> {
        self.open_monitored(rx, None).await
    }

    /// Opens an `Interface` for redirection and monitoring.
    pub async fn open_monitored(
        &mut self,
        rx: &mut Receiver,
        is_running: Option<Arc<AtomicBool>>,
    ) -> io::Result<()> {
        // Send gratuitous ARP
        if self.gw_ip_addr.is_some() {
            self.tx.lock().unwrap().send_gratuitous_arp()?;
        }
        let mut last_udp_cleanup = Instant::now();

        loop {
            if last_udp_cleanup.elapsed() >= UDP_CLEANUP_INTERVAL {
                self.prune_closed_udp_ports();
                self.defrag.prune_expired();
                let expired: Vec<_> = self.states.iter()
                    .filter(|(key, state)| self.streams.contains_key(key)
                        && state.is_idle(TCP_IDLE_TIMEOUT))
                    .map(|(key, _)| *key)
                    .collect();
                for (src, dst) in expired {
                    debug!("expire idle TCP connection {} -> {}", src, dst);
                    self.clean_up(src, dst);
                }
                last_udp_cleanup = Instant::now();
            }
            // Drop stale streams on the receiving task, which owns both state maps.
            // The pcap read timeout also wakes this loop on a quiet LAN.
            while let Ok((src, dst, id)) = self.tcp_timeout_rx.try_recv() {
                if self.stream_ids.get(&(src, dst)) == Some(&id) {
                    debug!("clean up stalled TCP connection {} -> {}", src, dst);
                    self.clean_up(src, dst);
                }
            }

            self.poll_connect_results();
            self.prune_abandoned_udp_associations();

            // Monitor
            if let Some(is_running) = &is_running {
                if !is_running.load(Ordering::Relaxed) {
                    return Ok(());
                }
            }
            match rx.next() {
                Ok(frame) => {
                    if let Some(ref indicator) = Indicator::from(frame) {
                        if let Some(t) = indicator.network_kind() {
                            match t {
                                LayerKinds::Arp => {
                                    if let Err(ref e) = self.handle_arp(indicator) {
                                        warn!("handle {}: {}", indicator.brief(), e);
                                    }
                                }
                                LayerKinds::Ipv4 => {
                                    if let Err(ref e) = self.handle_ipv4(indicator, frame).await {
                                        warn!("handle {}: {}", indicator.brief(), e);
                                    }
                                }
                                _ => unreachable!(),
                            }
                        }
                    };
                }
                Err(e) => {
                    if matches!(
                        e.kind(),
                        io::ErrorKind::TimedOut | io::ErrorKind::WouldBlock
                    ) {
                        thread::sleep(Duration::from_millis(TIMEDOUT_WAIT));
                        continue;
                    }
                    return Err(e);
                }
            };
        }
    }

    /// Accept completed proxy handshakes on the task that owns TCP/UDP maps.
    fn poll_connect_results(&mut self) {
        while let Ok((src, dst, id, result)) = self.tcp_ready_rx.try_recv() {
            let key = (src, dst);
            if self.pending_tcp.get(&key).map(|(generation, _)| *generation) != Some(id) {
                continue;
            }
            self.pending_tcp.remove(&key);
            match result {
                Ok(stream) => {
                    let worker = StreamWorker::from_connected(
                        self.get_tx(), src, dst, stream,
                        Some((self.tcp_timeout_tx.clone(), id)),
                        Arc::clone(&self.tcp_queued_bytes),
                    );
                    match worker {
                        Ok(worker) => {
                            self.stream_ids.insert(key, id);
                            self.streams.insert(key, worker);
                        }
                        Err(e) => self.fail_tcp_connect(src, dst, e),
                    }
                }
                Err(e) => self.fail_tcp_connect(src, dst, e),
            }
        }

        while let Ok((src, id, result)) = self.udp_ready_rx.try_recv() {
            if self.pending_udp.get(&src).map(|pending| pending.id) != Some(id) {
                continue;
            }
            let pending = self.pending_udp.remove(&src).unwrap();
            match result {
                Ok((worker, port)) => {
                    self.prune_closed_udp_ports();
                    if self.datagrams.contains_key(&port) || self.udp_lru.len() >= self.udp_lru.cap() {
                        debug!("discard UDP association at capacity or duplicate port: {}", src);
                        continue;
                    }
                    self.datagrams.insert(port, worker);
                    self.datagram_map.insert(src, port);
                    self.udp_lru.put(port, src);
                    for (payload, dst) in pending.datagrams {
                        if let Some(worker) = self.datagrams.get_mut(&port) {
                            if let Err(e) = worker.send_to(payload, dst) {
                                if e.kind() != io::ErrorKind::WouldBlock {
                                    warn!("queue UDP packet to proxy: {}", e);
                                }
                                break;
                            }
                        }
                    }
                }
                Err(e) => warn!("create UDP SOCKS association for {}: {}", src, e),
            }
        }
    }

    /// Aborted or panicked connectors must never consume pending slots forever.
    fn prune_abandoned_udp_associations(&mut self) {
        let expired: Vec<_> = self.pending_udp.iter()
            .filter(|(_, pending)| pending.started.elapsed() >= UDP_ASSOCIATE_DEADLINE)
            .map(|(&src, _)| src)
            .collect();
        for src in expired {
            if let Some(pending) = self.pending_udp.remove(&src) {
                pending.task.abort();
                warn!("expire unfinished SOCKS5 UDP association for {}", src);
            }
        }
    }

    fn fail_tcp_connect(&mut self, src: SocketAddrV4, dst: SocketAddrV4, error: io::Error) {
        warn!("SOCKS TCP connect {} -> {} failed: {}", src, dst, error);
        let reset = {
            let mut forwarder = self.tx.lock().unwrap();
            if let Some(state) = forwarder.get_state_mut(dst, src) {
                state.add_acknowledgement(1);
                forwarder.send_tcp_ack_rst(dst, src)
            } else {
                Ok(())
            }
        };
        if let Err(e) = reset {
            warn!("send TCP reset after proxy connect failure: {}", e);
        }
        self.clean_up(src, dst);
    }

    fn handle_arp(&mut self, indicator: &Indicator) -> io::Result<()> {
        if let Some(gw_ip_addr) = self.gw_ip_addr {
            if let Some(arp) = indicator.arp() {
                let src = arp.src();
                if src != self.local_ip_addr
                    && self.src_ip_addr.contains(src)
                    && arp.dst() == gw_ip_addr
                {
                    let src = arp.src();
                    trace!(
                        "receive from pcap: {} ({} Bytes)",
                        indicator.brief(),
                        indicator.len()
                    );

                    // Set forwarder's hardware address
                    self.set_tx_hardware_addr(src, arp.src_hardware_addr());

                    // Send
                    self.tx.lock().unwrap().send_arp_reply(src)?;

                    // Monitor
                    if let Some(size) = &self.traffic_size {
                        size.fetch_add(indicator.content_len(), Ordering::Relaxed);
                    }
                    if let Some(count) = &self.traffic_count {
                        count.fetch_add(1, Ordering::Relaxed);
                    }
                }
            }
        }

        Ok(())
    }

    async fn handle_ipv4(&mut self, indicator: &Indicator, frame: &[u8]) -> io::Result<()> {
        // Promiscuous capture also sees direct traffic sent to other routers.
        // Redirect only frames addressed to this gateway, before learning MACs
        // or reassembling fragments, or proxy egress can recurse through SOCKS.
        if indicator.ethernet().map(|ethernet| ethernet.dst())
            != Some(self.interface_hardware_addr)
        {
            return Ok(());
        }
        if let Some(ipv4) = indicator.ipv4() {
            let src = ipv4.src();
            if self.should_proxy_ipv4(src, ipv4.dst()) {
                let src = ipv4.src();
                trace!(
                    "receive from pcap: {} ({} + {} Bytes)",
                    indicator.brief(),
                    indicator.len(),
                    indicator.content_len() - indicator.len()
                );
                // Set forwarder's hardware address
                self.set_tx_hardware_addr(src, indicator.ethernet().unwrap().src());

                let frame_without_padding = &frame[..indicator.content_len()];
                if ipv4.is_fragment() {
                    // Fragmentation
                    let frag = match self.defrag.add(indicator, frame_without_padding) {
                        Some(frag) => frag,
                        None => return Ok(()),
                    };
                    let (transport, payload) = frag.concatenate();

                    if let Some(transport) = transport {
                        match transport {
                            Layers::Icmpv4(ref icmpv4) => self.handle_icmpv4(icmpv4)?,
                            Layers::Tcp(ref tcp) => self.handle_tcp(tcp, payload).await?,
                            Layers::Udp(ref udp) => self.handle_udp(udp, payload).await?,
                            _ => unreachable!(),
                        }
                    }
                } else {
                    #[allow(clippy::collapsible_if)]
                    if let Some(transport) = indicator.transport() {
                        match transport {
                            Layers::Icmpv4(icmpv4) => self.handle_icmpv4(icmpv4)?,
                            Layers::Tcp(tcp) => {
                                self.handle_tcp(tcp, &frame_without_padding[indicator.len()..])
                                    .await?
                            }
                            Layers::Udp(udp) => {
                                self.handle_udp(udp, &frame_without_padding[indicator.len()..])
                                    .await?
                            }
                            _ => unreachable!(),
                        }
                    }
                }

                // Monitor
                if let Some(size) = &self.traffic_size {
                    size.fetch_add(indicator.content_len(), Ordering::Relaxed);
                }
                if let Some(count) = &self.traffic_count {
                    count.fetch_add(1, Ordering::Relaxed);
                }
            }
        }

        Ok(())
    }

    fn handle_icmpv4(&mut self, icmpv4: &Icmpv4) -> io::Result<()> {
        if icmpv4.is_destination_port_unreachable() {
            // Destination port unreachable
            let kind = match icmpv4.next_level_layer_kind() {
                Some(kind) => kind,
                None => return Ok(()),
            };
            #[allow(clippy::single_match)]
            match kind {
                LayerKinds::Udp => {
                    // An ICMP error may quote fewer than eight UDP header bytes.
                    if let Some(dst) = icmpv4.dst() {
                        self.unbind_local_udp_port(dst);
                    }
                }
                _ => {}
            }
        } else if icmpv4.is_fragmentation_required_and_df_flag_set() {
            // Fragmentation required, and DF flag set
            // The quoted IPv4 packet and the next-hop MTU are both untrusted.
            let (Some(mtu), Some(dst_ip_addr)) =
                (icmpv4.next_hop_mtu(), icmpv4.dst_ip_addr())
            else {
                return Ok(());
            };
            if self
                .tx
                .lock()
                .unwrap()
                .set_src_mtu(dst_ip_addr, mtu as usize)
            {
                info!("Update MTU of {} to {}", dst_ip_addr, mtu);
            }
        }

        Ok(())
    }

    async fn handle_tcp(&mut self, tcp: &Tcp, payload: &[u8]) -> io::Result<()> {
        if tcp.is_rst() {
            self.handle_tcp_rst(tcp);
        } else if tcp.is_ack() {
            self.handle_tcp_ack(tcp, payload)?;
        } else if tcp.is_syn() {
            // Pure TCP SYN
            self.handle_tcp_syn(tcp).await?;
        } else if tcp.is_fin() {
            // Pure TCP FIN
            self.handle_tcp_fin(tcp, payload)?;
        } else {
            // Flags come from the network and are not an internal invariant.
            trace!("drop TCP segment with unsupported flags: {}", tcp.flag_string());
        }

        Ok(())
    }

    fn handle_tcp_ack(&mut self, tcp: &Tcp, payload: &[u8]) -> io::Result<()> {
        let src = SocketAddrV4::new(tcp.src_ip_addr(), tcp.src());
        let dst = SocketAddrV4::new(tcp.dst_ip_addr(), tcp.dst());
        let key = (src, dst);
        let is_exist = self.streams.get(&key).is_some();
        let is_writable = match self.streams.get(&key) {
            Some(stream) => !stream.is_tx_closed(),
            None => false,
        };

        if is_exist {
            // ACK
            let state = self
                .states
                .get_mut(&key)
                .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
            state.touch();
            if tcp.sequence() != state.recv_next() {
                trace!(
                    "TCP out of order of {} -> {} at {}",
                    src,
                    dst,
                    tcp.sequence()
                );
            }
            {
                let mut tx_locked = self.tx.lock().unwrap();
                let tx_state = tx_locked
                    .get_state_mut(dst, src)
                    .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;

                tx_state.acknowledge(tcp.acknowledgement());
                tx_state.set_src_window((tcp.window() as usize) << state.wscale() as usize);
            }

            if !payload.is_empty() {
                // ACK
                if is_writable {
                    // Append to cache
                    let cont_payload = state.append_cache(tcp.sequence(), payload)?;

                    // SACK
                    if state.sack_perm() {
                        let sacks = state.cache().filled();
                        self.tx
                            .lock()
                            .unwrap()
                            .get_state_mut(dst, src)
                            .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?
                            .set_sacks(&sacks);
                    }

                    match cont_payload {
                        Some(payload) => {
                            // Send
                            let stream = self
                                .streams
                                .get_mut(&key)
                                .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
                            let size = payload.len();
                            match stream.send(payload) {
                                Ok(_) => {
                                    let cache_remaining_size = (state.cache().remaining()
                                        >> state.recv_wscale() as usize)
                                        as u16;

                                    state.add_recv_next(size as u32);

                                    let mut tx_locked = self.tx.lock().unwrap();
                                    let tx_state = tx_locked
                                        .get_state_mut(dst, src)
                                        .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;

                                    // Update window size
                                    tx_state.set_window(cache_remaining_size);

                                    // Update TCP acknowledgement
                                    tx_state.add_acknowledgement(size as u32);

                                    // Send delayed ACK0
                                    // If there is a heavy traffic, the ACK reported may be inaccurate, which would results in retransmission
                                    tx_locked.send_tcp_delay_ack_0(dst, src)?;
                                }
                                Err(e) => {
                                    // Send ACK/RST
                                    self.tx.lock().unwrap().send_tcp_ack_rst(dst, src)?;

                                    // Clean up
                                    self.clean_up(src, dst);

                                    return Err(e);
                                }
                            }
                        }
                        None => {
                            // Retransmission or unordered
                            let cache_remaining_size =
                                (state.cache().remaining() >> state.recv_wscale() as usize) as u16;

                            // Update window size
                            let mut tx_locked = self.tx.lock().unwrap();
                            let tx_state = tx_locked
                                .get_state_mut(dst, src)
                                .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;

                            tx_state.set_window(cache_remaining_size);

                            // Send ACK0
                            tx_locked.send_tcp_ack_0(dst, src)?;
                        }
                    }
                } else {
                    // Send ACK/RST
                    self.tx.lock().unwrap().send_tcp_ack_rst(dst, src)?;

                    // Clean up
                    self.clean_up(src, dst);

                    return Ok(());
                }
            } else {
                // ACK0
                if !is_writable {
                    if self.tx.lock().unwrap().get_cache_size(dst, src) == 0 {
                        // LAST_ACK
                        // Clean up
                        self.clean_up(src, dst);

                        return Ok(());
                    }
                } else {
                    // Duplicate ACK
                    state.admit(tcp.acknowledgement());
                    if state.duplicate() >= DUPLICATES_THRESHOLD {
                        let is_cooled_down = match state.last_retrans() {
                            Some(instant) => instant.elapsed().as_millis() < RETRANS_COOL_DOWN,
                            None => false,
                        };

                        if !is_cooled_down && !tcp.is_zero_window() {
                            // Fast retransmit
                            let mut is_sr = false;
                            if state.sack_perm() {
                                if let Some(sacks) = tcp.sack() {
                                    if !sacks.is_empty() {
                                        // Selective retransmission
                                        self.tx.lock().unwrap().retransmit_tcp(
                                            dst,
                                            src,
                                            Some(sacks),
                                        )?;
                                        is_sr = true;
                                    }
                                }
                            }

                            if !is_sr {
                                // Back N
                                self.tx.lock().unwrap().retransmit_tcp(dst, src, None)?;
                            }

                            state.admit_retrans();
                        }
                    }
                }
            }

            // Trigger sending remaining data
            self.tx.lock().unwrap().send_tcp(dst, src)?;

            // FIN
            if tcp.is_fin() || state.fin_sequence().is_some() {
                self.handle_tcp_fin(tcp, payload)?;
            }
        } else {
            // Send ACK/RST
            self.tx
                .lock()
                .unwrap()
                .send_tcp_ack_rst_untracked(dst, src, tcp.acknowledgement())?;
        }

        Ok(())
    }

    async fn handle_tcp_syn(&mut self, tcp: &Tcp) -> io::Result<()> {
        let src = SocketAddrV4::new(tcp.src_ip_addr(), tcp.src());
        let dst = SocketAddrV4::new(tcp.dst_ip_addr(), tcp.dst());
        let key = (src, dst);
        let is_exist = self.streams.contains_key(&key) || self.pending_tcp.contains_key(&key);

        // Connect if not connected, drop if established
        if !is_exist {
            if self.streams.len() + self.pending_tcp.len() >= MAX_TCP_STREAMS
                || self.pending_tcp.len() >= MAX_PENDING_TCP_CONNECTS {
                // Do not evict an unrelated live connection to make room.
                debug!("drop TCP SYN at active connection limit: {} -> {}", src, dst);
                return Ok(());
            }
            // Clean up
            self.clean_up(src, dst);

            // Admit SYN
            // RFC 7323 limits TCP window scale to 14.
            let wscale = match ENABLE_WSCALE {
                true => tcp.wscale().filter(|&scale| scale <= 14),
                false => None,
            };
            // Our advertised scale is independent of the peer's scale.
            let recv_wscale = wscale.map(|_| MAX_RECV_WSCALE);
            let sack_perm = ENABLE_SACK && tcp.is_sack_perm();
            let mut state = TcpRxState::new(
                src, dst, tcp.sequence(), wscale.unwrap_or(0),
                recv_wscale.unwrap_or(0), sack_perm,
            );
            state.set_cache_budget(Arc::clone(&self.tcp_rx_cache_budget));

            {
                let mut tx_locked = self.tx.lock().unwrap();

                let mut rng = rand::thread_rng();
                let sequence = rng.r#gen::<u32>();
                let acknowledgement = tcp.sequence().wrapping_add(1);
                if let Some(mss) = tcp.mss() {
                    let mtu = Ipv4::minimum_len() + Tcp::minimum_len() + mss as usize;
                    if tx_locked.set_src_mtu(tcp.src_ip_addr(), mtu) {
                        info!("Update MTU of {} to {}", tcp.src_ip_addr(), mtu);
                    }
                }

                let mut tx_state = TcpTxState::new(
                    src,
                    dst,
                    sequence,
                    acknowledgement,
                    tcp.window(),
                    recv_wscale,
                    sack_perm,
                    wscale,
                    tx_locked.get_src_mtu(tcp.src_ip_addr())
                        - (Ipv4::minimum_len() + Tcp::minimum_len()),
                );
                tx_state.set_send_budget(Arc::clone(&self.tcp_tx_cache_budget));
                tx_locked.set_state(dst, src, tx_state);
            }

            // Connect asynchronously. Only the owner loop can install a result.
            self.next_stream_id = self.next_stream_id.wrapping_add(1);
            let stream_id = self.next_stream_id;
            self.states.insert(key, state);
            let sender = self.tcp_ready_tx.clone();
            let proxy = self.proxy.clone();
            let handle = tokio::spawn(async move {
                let result = proxy.connect_tcp(dst).await;
                let _ = sender.send((src, dst, stream_id, result));
            });
            self.pending_tcp.insert(key, (stream_id, handle));
        }

        Ok(())
    }

    fn handle_tcp_rst(&mut self, tcp: &Tcp) {
        let src = SocketAddrV4::new(tcp.src_ip_addr(), tcp.src());
        let dst = SocketAddrV4::new(tcp.dst_ip_addr(), tcp.dst());
        let key = (src, dst);

        // Validate every RST against RCV.NXT, regardless of the ACK flag.
        // A matching four-tuple alone must not allow a stale RST to tear down
        // an established connection.
        match self.states.get(&key).map(|state| state.recv_next()) {
            Some(recv_next) if tcp.sequence() == recv_next => {
                self.clean_up(src, dst);
            }
            Some(recv_next) => {
                trace!(
                    "ignore TCP RST of {} -> {} at {} (expected {})",
                    src,
                    dst,
                    tcp.sequence(),
                    recv_next
                );
            }
            None => {
                // Preserve cleanup of pending or otherwise untracked connections.
                self.clean_up(src, dst);
            }
        }
    }

    fn handle_tcp_fin(&mut self, tcp: &Tcp, payload: &[u8]) -> io::Result<()> {
        let src = SocketAddrV4::new(tcp.src_ip_addr(), tcp.src());
        let dst = SocketAddrV4::new(tcp.dst_ip_addr(), tcp.dst());
        let key = (src, dst);
        let is_exist = self.streams.get(&key).is_some();
        let (is_writable, is_readable) = match self.streams.get(&key) {
            Some(stream) => (!stream.is_tx_closed(), !stream.is_rx_closed()),
            None => (false, false),
        };

        if is_exist {
            if is_writable {
                let state = self
                    .states
                    .get_mut(&key)
                    .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
                if tcp.is_fin() {
                    // Update FIN sequence
                    state.set_fin_sequence(
                        tcp.sequence().wrapping_add(payload.len() as u32),
                    );
                }

                // If the receive next is the same as the FIN sequence, the FIN should be popped
                if let Some(fin_sequence) = state.fin_sequence() {
                    if fin_sequence == state.recv_next() {
                        // Admit FIN
                        state.admit_fin();
                        state.add_recv_next(1);

                        {
                            let mut tx_locked = self.tx.lock().unwrap();
                            let tx_state = tx_locked
                                .get_state_mut(dst, src)
                                .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;

                            tx_state.add_acknowledgement(1);

                            // Send ACK0
                            tx_locked.send_tcp_ack_0(dst, src)?;
                        }
                        if is_readable {
                            // Close by local
                            let stream = self
                                .streams
                                .get_mut(&key)
                                .ok_or_else(|| io::Error::from(io::ErrorKind::NotFound))?;
                            stream.shutdown(Shutdown::Write);
                        } else {
                            // Close by remote
                            // Clean up
                            self.clean_up(src, dst);
                        }
                    } else {
                        trace!(
                            "TCP out of order of {} -> {} at {}",
                            src,
                            dst,
                            tcp.sequence()
                        );

                        if payload.is_empty() {
                            // Send ACK0
                            self.tx.lock().unwrap().send_tcp_ack_0(dst, src)?;
                        }
                    }
                }
            } else {
                // Retransmission
                // Send ACK0
                self.tx.lock().unwrap().send_tcp_ack_0(dst, src)?;
            }
        } else {
            // Send ACK/RST
            self.tx
                .lock()
                .unwrap()
                .send_tcp_ack_rst_untracked(dst, src, tcp.acknowledgement())?;
        }

        Ok(())
    }

    fn clean_up(&mut self, src: SocketAddrV4, dst: SocketAddrV4) {
        let key = (src, dst);

        if let Some((_, handle)) = self.pending_tcp.remove(&key) {
            handle.abort();
        }
        self.stream_ids.remove(&key);
        self.streams.remove(&key);
        self.states.remove(&key);

        self.tx.lock().unwrap().clean_up(dst, src);
    }

    async fn handle_udp(&mut self, udp: &Udp, payload: &[u8]) -> io::Result<()> {
        let src = SocketAddrV4::new(udp.src_ip_addr(), udp.src());
        let dst = SocketAddrV4::new(udp.dst_ip_addr(), udp.dst());
        if let Some(&port) = self.datagram_map.get(&src) {
            if self.datagrams.get(&port).is_some_and(|worker| !worker.is_closed())
                && self.udp_lru.get(&port) == Some(&src)
            {
                let result = self.datagrams.get_mut(&port).unwrap().send_to(payload.to_vec(), dst);
                // UDP is lossy by design: a full bounded channel drops this datagram.
                match result {
                    Ok(()) => return Ok(()),
                    Err(e) if e.kind() == io::ErrorKind::WouldBlock => return Ok(()),
                    Err(_) => {},
                }
            }
            self.unbind_local_udp_port(src);
        }
        if let Some(pending) = self.pending_udp.get_mut(&src) {
            if pending.datagrams.len() < MAX_PENDING_UDP_DATAGRAMS {
                pending.datagrams.push_back((payload.to_vec(), dst));
            }
            return Ok(());
        }
        if self.pending_udp.len() >= MAX_PENDING_UDP_ASSOCIATIONS {
            return Ok(());
        }
        if self.udp_lru.len() >= self.udp_lru.cap() {
            self.prune_udp_ports(UDP_PRESSURE_IDLE_TIMEOUT);
            // Do not evict a recently active game session to accept a new port.
            if self.udp_lru.len() >= self.udp_lru.cap() {
                return Ok(());
            }
        }
        self.next_udp_id = self.next_udp_id.wrapping_add(1);
        let id = self.next_udp_id;
        let sender = self.udp_ready_tx.clone();
        let proxy = self.proxy.clone();
        let forwarder = self.get_tx();
        let task = tokio::spawn(async move {
            let result = DatagramWorker::bind(forwarder, src, &proxy).await;
            let _ = sender.send((src, id, result));
        });
        let mut datagrams = VecDeque::new();
        datagrams.push_back((payload.to_vec(), dst));
        self.pending_udp.insert(src, PendingUdpAssociation {
            id,
            started: Instant::now(),
            task,
            datagrams,
        });
        Ok(())
    }

    fn prune_closed_udp_ports(&mut self) {
        self.prune_udp_ports(UDP_IDLE_TIMEOUT);
    }

    fn prune_udp_ports(&mut self, idle_timeout: Duration) {
        let closed: Vec<u16> = self
            .datagrams
            .iter()
            .filter_map(|(&port, worker)|
                (worker.is_closed() || worker.is_idle(idle_timeout)).then_some(port))
            .collect();
        for port in closed {
            if let Some(src) = self.udp_lru.pop(&port) {
                self.datagram_map.remove(&src);
                debug!("remove closed UDP association {} = {}", port, src);
            }
            self.datagrams.remove(&port);
        }
    }

    fn unbind_local_udp_port(&mut self, src: SocketAddrV4) {
        let local_port = self.datagram_map.get(&src);
        if let Some(&local_port) = local_port {
            self.datagrams.remove(&local_port);
            self.udp_lru.pop(&local_port);
            self.datagram_map.remove(&src);

            trace!("unbind UDP port {} = {}", local_port, src);
        }
    }

    fn get_tx(&self) -> Arc<Mutex<Forwarder>> {
        Arc::clone(&self.tx)
    }

    fn set_tx_hardware_addr(&mut self, ip_addr: Ipv4Addr, hardware_addr: HardwareAddr) {
        if self.tx.lock().unwrap().set_src_hardware_addr(ip_addr, hardware_addr) {
            info!("Device {} ({}) joined or updated its address", ip_addr, hardware_addr);
        }
    }
}

#[cfg(test)]
mod ethernet_destination_tests {
    use super::*;
    use pnet::util::MacAddr;

    const HOST_MAC: HardwareAddr = MacAddr(2, 0, 0, 0, 0, 10);
    const ROUTER_MAC: HardwareAddr = MacAddr(2, 0, 0, 0, 0, 1);
    const CLIENT_MAC: HardwareAddr = MacAddr(2, 0, 0, 0, 0, 101);
    const CLIENT: Ipv4Addr = Ipv4Addr::new(192, 168, 1, 101);

    fn redirector() -> Redirector {
        let host = Ipv4Addr::new(192, 168, 1, 10);
        let gateway = Ipv4Addr::new(192, 168, 1, 250);
        let forwarder = Forwarder::new(Box::new(pcap::BlackHole::new()), 1500, HOST_MAC, host);
        Redirector::new(
            Arc::new(Mutex::new(forwarder)),
            Ipv4Network::new(CLIENT, 32).unwrap(),
            gateway,
            Some(gateway),
            ProxyConfig::new_socks(SocketAddrV4::new(host, 1083), false, false, None),
            None,
        )
    }

    fn frame(mac: HardwareAddr, ipv4: Ipv4, transport: Option<Layers>, payload: &[u8]) -> Vec<u8> {
        let indicator = Indicator::new(
            Layers::Ethernet(Ethernet::new(LayerKinds::Ipv4, CLIENT_MAC, mac).unwrap()),
            Some(Layers::Ipv4(ipv4)),
            transport,
        );
        let mut frame = vec![0; indicator.len() + payload.len()];
        indicator
            .serialize_with_payload(&mut frame, payload)
            .unwrap();
        frame
    }

    async fn deliver(redirector: &mut Redirector, frame: &[u8]) {
        let indicator = Indicator::from(frame).unwrap();
        redirector.handle_ipv4(&indicator, frame).await.unwrap();
    }

    #[tokio::test]
    async fn direct_tcp_egress_does_not_consume_proxy_slots() {
        let mut redirector = redirector();
        let dst = Ipv4Addr::new(10, 3, 1, 1);
        // A valid TCP SYN, targeting the upstream endpoint seen in the logs.
        let mut syn = [0u8; 20];
        syn[2..4].copy_from_slice(&1776u16.to_be_bytes());
        syn[12] = 0x50;
        syn[13] = 0x02;
        syn[14..16].copy_from_slice(&65535u16.to_be_bytes());
        for port in 40000u16..40300 {
            syn[..2].copy_from_slice(&port.to_be_bytes());
            let ipv4 = Ipv4::new(0, LayerKinds::Tcp, CLIENT, dst).unwrap();
            deliver(&mut redirector, &frame(ROUTER_MAC, ipv4, None, &syn)).await;
        }
        assert!(redirector.pending_tcp.is_empty());
        assert!(redirector.states.is_empty());
        assert!(
            redirector
                .tx
                .lock()
                .unwrap()
                .src_hardware_addr_map
                .is_empty()
        );

        // The same IP destination still proxies when routed through our MAC.
        let ipv4 = Ipv4::new(0, LayerKinds::Tcp, CLIENT, dst).unwrap();
        deliver(&mut redirector, &frame(HOST_MAC, ipv4, None, &syn)).await;
        let src = SocketAddrV4::new(CLIENT, 40299);
        let dst = SocketAddrV4::new(dst, 1776);
        assert!(redirector.pending_tcp.contains_key(&(src, dst)));
        assert!(redirector.states.contains_key(&(src, dst)));
        redirector.clean_up(src, dst);
    }

    #[tokio::test]
    async fn only_gateway_addressed_udp_creates_an_association() {
        let mut redirector = redirector();
        let ipv4 = Ipv4::new(0, LayerKinds::Udp, CLIENT, Ipv4Addr::new(8, 8, 8, 8)).unwrap();
        let udp = Udp::new(40000, 53);
        for mac in [ROUTER_MAC, pcap::HARDWARE_ADDR_BROADCAST] {
            deliver(
                &mut redirector,
                &frame(mac, ipv4.clone(), Some(Layers::Udp(udp.clone())), b"dns"),
            )
            .await;
        }
        assert!(redirector.pending_udp.is_empty());
        assert!(
            redirector
                .tx
                .lock()
                .unwrap()
                .src_hardware_addr_map
                .is_empty()
        );

        deliver(
            &mut redirector,
            &frame(HOST_MAC, ipv4, Some(Layers::Udp(udp)), b"dns"),
        )
        .await;
        assert_eq!(redirector.pending_udp.len(), 1);
        for (_, pending) in redirector.pending_udp.drain() {
            pending.task.abort();
        }
    }

    #[tokio::test]
    async fn direct_fragments_do_not_enter_gateway_reassembly() {
        let mut redirector = redirector();
        let dst = Ipv4Addr::new(8, 8, 8, 8);
        let first = Ipv4::new_more_fragment(42, LayerKinds::Udp, 0, CLIENT, dst).unwrap();
        let last = Ipv4::new_last_fragment(42, LayerKinds::Udp, 1, CLIENT, dst).unwrap();
        let udp = [0x9c, 0x40, 0, 53, 0, 16, 0, 0];

        deliver(
            &mut redirector,
            &frame(ROUTER_MAC, first.clone(), None, &udp),
        )
        .await;
        deliver(&mut redirector, &frame(HOST_MAC, last, None, b"12345678")).await;
        assert!(redirector.pending_udp.is_empty());

        deliver(&mut redirector, &frame(HOST_MAC, first, None, &udp)).await;
        assert_eq!(redirector.pending_udp.len(), 1);
        for (_, pending) in redirector.pending_udp.drain() {
            pending.task.abort();
        }
    }
}

#[cfg(test)]
mod local_destination_tests {
    use super::*;

    #[test]
    fn host_service_is_not_proxied_but_wireguard_destination_is() {
        let host = Ipv4Addr::new(192, 168, 1, 10);
        let gateway = Ipv4Addr::new(192, 168, 1, 250);
        let client = Ipv4Addr::new(192, 168, 1, 101);
        let forwarder = Forwarder::new(
            Box::new(pcap::BlackHole::new()),
            1500,
            pcap::HARDWARE_ADDR_UNSPECIFIED,
            host,
        );
        let redirector = Redirector::new(
            Arc::new(Mutex::new(forwarder)),
            Ipv4Network::new(client, 32).unwrap(),
            gateway,
            Some(gateway),
            ProxyConfig::new_socks(SocketAddrV4::new(host, 1083), false, false, None),
            None,
        );

        assert_eq!(redirector.interface_ip_addr, host);
        assert!(!redirector.should_proxy_ipv4(client, host));
        assert!(redirector.should_proxy_ipv4(client, Ipv4Addr::new(192, 168, 2, 200)));
        assert!(redirector.should_proxy_ipv4(client, Ipv4Addr::new(8, 8, 8, 8)));
        assert!(!redirector.should_proxy_ipv4(Ipv4Addr::new(192, 168, 1, 102), host));
    }
}

#[cfg(test)]
mod tcp_segmentation_tests {
    use super::Forwarder;

    #[test]
    fn fin_is_only_attached_to_the_final_segment() {
        assert!(!Forwarder::fin_for_segment(true, 1460, 3000));
        assert!(!Forwarder::fin_for_segment(true, 2920, 3000));
        assert!(Forwarder::fin_for_segment(true, 3000, 3000));
        assert!(!Forwarder::fin_for_segment(false, 3000, 3000));
    }
}

#[cfg(test)]
mod tcp_rst_validation_tests {
    use super::*;

    fn redirector() -> Redirector {
        let local = Ipv4Addr::new(192, 0, 2, 250);
        let forwarder = Forwarder::new(
            Box::new(pcap::BlackHole::new()),
            1500,
            pcap::HARDWARE_ADDR_UNSPECIFIED,
            local,
        );
        Redirector::new(
            Arc::new(Mutex::new(forwarder)),
            Ipv4Network::new(Ipv4Addr::new(192, 0, 2, 0), 24).unwrap(),
            local,
            None,
            ProxyConfig::new_socks(
                SocketAddrV4::new(Ipv4Addr::LOCALHOST, 1080), false, false, None,
            ),
            None,
        )
    }

    fn rst_packet(src: SocketAddrV4, dst: SocketAddrV4, sequence: u32) -> Tcp {
        let mut tcp = Tcp::new_rst(src.port(), dst.port(), sequence, 0, 0, None);
        let ipv4 = Ipv4::new(0, LayerKinds::Tcp, *src.ip(), *dst.ip()).unwrap();
        tcp.set_ipv4_layer(&ipv4);
        tcp
    }

    fn add_connection(
        redirector: &mut Redirector,
        src: SocketAddrV4,
        dst: SocketAddrV4,
        recv_next: u32,
    ) {
        redirector.states.insert(
            (src, dst),
            TcpRxState::new(src, dst, recv_next.wrapping_sub(1), 0, 0, false),
        );
    }

    #[test]
    fn rst_without_ack_with_wrong_sequence_does_not_remove_connection() {
        let src = SocketAddrV4::new(Ipv4Addr::new(192, 0, 2, 1), 40000);
        let dst = SocketAddrV4::new(Ipv4Addr::new(198, 51, 100, 1), 443);
        let recv_next = 1000;
        let mut redirector = redirector();
        add_connection(&mut redirector, src, dst, recv_next);

        redirector.handle_tcp_rst(&rst_packet(src, dst, recv_next.wrapping_add(1)));

        assert!(redirector.states.contains_key(&(src, dst)));
    }

    #[test]
    fn rst_without_ack_with_exact_sequence_removes_connection() {
        let src = SocketAddrV4::new(Ipv4Addr::new(192, 0, 2, 1), 40000);
        let dst = SocketAddrV4::new(Ipv4Addr::new(198, 51, 100, 1), 443);
        let recv_next = 1000;
        let mut redirector = redirector();
        add_connection(&mut redirector, src, dst, recv_next);

        redirector.handle_tcp_rst(&rst_packet(src, dst, recv_next));

        assert!(!redirector.states.contains_key(&(src, dst)));
    }

    #[test]
    fn rst_sequence_validation_handles_wraparound() {
        let src = SocketAddrV4::new(Ipv4Addr::new(192, 0, 2, 1), 40000);
        let dst = SocketAddrV4::new(Ipv4Addr::new(198, 51, 100, 1), 443);
        let mut redirector = redirector();
        add_connection(&mut redirector, src, dst, 0);

        redirector.handle_tcp_rst(&rst_packet(src, dst, u32::MAX));
        assert!(redirector.states.contains_key(&(src, dst)));

        redirector.handle_tcp_rst(&rst_packet(src, dst, 0));
        assert!(!redirector.states.contains_key(&(src, dst)));
    }
}

#[cfg(test)]
mod malformed_icmp_tests {
    use super::*;
    use pnet::packet::icmp::{destination_unreachable, Icmp, IcmpTypes};

    fn redirector() -> Redirector {
        let local = Ipv4Addr::new(192, 0, 2, 250);
        let forwarder = Forwarder::new(
            Box::new(pcap::BlackHole::new()),
            1500,
            pcap::HARDWARE_ADDR_UNSPECIFIED,
            local,
        );
        Redirector::new(
            Arc::new(Mutex::new(forwarder)),
            Ipv4Network::new(Ipv4Addr::new(192, 0, 2, 0), 24).unwrap(),
            local,
            None,
            ProxyConfig::new_socks(
                SocketAddrV4::new(Ipv4Addr::LOCALHOST, 1080), false, false, None,
            ),
            None,
        )
    }

    #[test]
    fn ignore_port_unreachable_without_quoted_udp_header() {
        // A complete quoted IPv4 header identifies UDP, but has no UDP ports.
        let mut quote = [0u8; 20];
        quote[0] = 0x45;
        quote[2..4].copy_from_slice(&20u16.to_be_bytes());
        quote[9] = 17;
        let error = Icmpv4::new_destination_port_unreachable(&quote);
        assert_eq!(error.next_level_layer_kind(), Some(LayerKinds::Udp));
        assert_eq!(error.dst(), None);
        assert!(redirector().handle_icmpv4(&error).is_ok());
    }

    #[test]
    fn ignore_fragmentation_needed_without_quoted_ipv4_header() {
        let error = Icmpv4::from(Icmp {
            icmp_type: IcmpTypes::DestinationUnreachable,
            icmp_code: destination_unreachable::IcmpCodes::FragmentationRequiredAndDFFlagSet,
            checksum: 0,
            payload: vec![0, 0, 0x05, 0xdc],
        });
        assert_eq!(error.next_hop_mtu(), Some(1500));
        assert_eq!(error.dst_ip_addr(), None);
        assert!(redirector().handle_icmpv4(&error).is_ok());
    }

    #[test]
    fn ignore_quoted_ipv4_header_with_invalid_ihl() {
        let mut quote = [0u8; 20];
        quote[0] = 0x4f; // IHL claims 60 bytes, only 20 are present.
        quote[9] = 17;
        let error = Icmpv4::new_destination_port_unreachable(&quote);
        assert_eq!(error.next_level_layer_kind(), None);
        assert!(redirector().handle_icmpv4(&error).is_ok());
    }
}
