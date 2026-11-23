//! Support for handling SOCKS proxies.

use async_socks5::{self, AddrKind, Auth};
use log::trace;
use std::net::{Ipv4Addr, SocketAddr, SocketAddrV4};
use std::sync::Arc;
use tokio::io::{self, BufStream};
use tokio::net::{TcpStream, UdpSocket};

/// Represents the username and the password of the authentication connecting to a SOCKS5 server.
#[derive(Clone, Debug)]
pub struct SocksAuth {
    username: String,
    password: String,
}

impl SocksAuth {
    /// Creates a `SocksAuth`.
    pub fn new(username: String, password: String) -> SocksAuth {
        SocksAuth { username, password }
    }
}

/// Represents the options connecting to a SOCKS5 server.
#[derive(Clone, Debug)]
pub struct SocksOption {
    force_associate_remote: bool,
    force_associate_bind_addr: bool,
    auth: Option<SocksAuth>,
}

impl SocksOption {
    /// Creates a `SocksOption`.
    pub fn new(
        force_associate_remote: bool,
        force_associate_bind_addr: bool,
        auth: Option<SocksAuth>,
    ) -> SocksOption {
        SocksOption {
            force_associate_remote,
            force_associate_bind_addr,
            auth,
        }
    }

    fn auth(&self) -> Option<Auth> {
        self.auth
            .as_ref()
            .map(|auth| {
                Auth::new(auth.username.clone(), auth.password.clone())
            })
    }
}

/// Connects to a target server through a SOCKS5 proxy.
pub async fn connect(
    remote: SocketAddrV4,
    dst: SocketAddrV4,
    options: &SocksOption,
) -> io::Result<BufStream<TcpStream>> {
    let stream = TcpStream::connect(remote).await?;
    let mut stream = BufStream::new(stream);
    if let Err(e) = async_socks5::connect(&mut stream, dst, options.auth()).await {
        return match e {
            async_socks5::Error::Io(e) => Err(e),
            _ => Err(io::Error::new(io::ErrorKind::Other, e)),
        }
    }

    Ok(stream)
}

const RSV_SIZE: usize = 2;
const FRAG_SIZE: usize = 1;
const ATYP_SIZE: usize = 1;
const DST_ADDR_SIZE: usize = 4;
const DST_PORT_SIZE: usize = 2;
const HEADER_SIZE: usize = RSV_SIZE + FRAG_SIZE + ATYP_SIZE + DST_ADDR_SIZE + DST_PORT_SIZE;

const ATYP_IPV4: u8 = 1;

fn parse_udp_source(datagram: &[u8]) -> Option<SocketAddrV4> {
    if datagram.len() < HEADER_SIZE
        || datagram[0] != 0
        || datagram[1] != 0
        || datagram[2] != 0
        || datagram[3] != ATYP_IPV4
    {
        return None;
    }

    Some(SocketAddrV4::new(
        Ipv4Addr::new(datagram[4], datagram[5], datagram[6], datagram[7]),
        u16::from_be_bytes([datagram[8], datagram[9]]),
    ))
}

/// Represents the send half of a SOCKS5 UDP client.
#[allow(dead_code)]
#[derive(Debug)]
pub struct SocksSendHalf {
    stream: Arc<BufStream<TcpStream>>,
    socket: Arc<UdpSocket>,
}

impl SocksSendHalf {
    /// Creates a new `SocksSendHalf`.
    pub fn new(stream: Arc<BufStream<TcpStream>>, socket: Arc<UdpSocket>) -> SocksSendHalf {
        SocksSendHalf { stream, socket }
    }

    /// Sends data on the socket to the given address.
    pub async fn send_to(&mut self, payload: &[u8], dst: SocketAddrV4) -> io::Result<usize> {
        let mut buf = vec![0u8; HEADER_SIZE + payload.len()];
        // RSV
        // FRAG
        // ATYP
        buf[3] = ATYP_IPV4;
        // DST.ADDR
        buf[4..8].copy_from_slice(&dst.ip().octets());
        // DST.PORT
        buf[8] = (dst.port() / 256) as u8;
        buf[9] = (dst.port() % 256) as u8;
        // Data
        buf[10..].copy_from_slice(payload);

        self.socket.send(buf.as_slice()).await
    }
}

/// Represents the receive half of a SOCKS5 UDP client.
#[allow(dead_code)]
#[derive(Debug)]
pub struct SocksRecvHalf {
    stream: Arc<BufStream<TcpStream>>,
    socket: Arc<UdpSocket>,
    buffer: Vec<u8>,
}

impl SocksRecvHalf {
    /// Creates a new `SocksRecvHalf`.
    pub fn new(stream: Arc<BufStream<TcpStream>>, socket: Arc<UdpSocket>) -> SocksRecvHalf {
        SocksRecvHalf {
            stream,
            socket,
            buffer: vec![0u8; u16::MAX as usize],
        }
    }

    /// Receives UDP packets and detects closure of the SOCKS5 control connection.
    pub async fn recv_from(&mut self, buffer: &mut [u8]) -> io::Result<(usize, SocketAddrV4)> {
        loop {
            let n = tokio::select! {
                result = self.socket.recv(&mut self.buffer) => result?,
                result = self.stream.get_ref().readable() => {
                    result?;
                    let mut byte = [0u8; 1];
                    match self.stream.get_ref().try_read(&mut byte) {
                        Err(ref e) if e.kind() == io::ErrorKind::WouldBlock => continue,
                        Err(e) => return Err(e),
                        Ok(_) => return Err(io::Error::new(
                            io::ErrorKind::ConnectionAborted,
                            "SOCKS5 UDP association control connection closed",
                        )),
                    }
                }
            };

            let addr = match parse_udp_source(&self.buffer[..n]) {
                Some(addr) => addr,
                None => {
                    trace!("drop invalid SOCKS5 UDP datagram");
                    continue;
                }
            };
            let size = n - HEADER_SIZE;
            if size > buffer.len() {
                return Err(io::Error::new(io::ErrorKind::InvalidData, "UDP buffer too small"));
            }
            buffer[..size].copy_from_slice(&self.buffer[HEADER_SIZE..n]);
            return Ok((size, addr));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_udp_source_validates_header() {
        let valid = [0, 0, 0, ATYP_IPV4, 1, 2, 3, 4, 0x12, 0x34];
        assert_eq!(
            parse_udp_source(&valid),
            Some(SocketAddrV4::new(Ipv4Addr::new(1, 2, 3, 4), 0x1234))
        );
        assert_eq!(parse_udp_source(&valid[..9]), None);
        for index in 0..4 {
            let mut invalid = valid;
            invalid[index] = 0xff;
            assert_eq!(parse_udp_source(&invalid), None);
        }
    }
}

/// Binds a local address to a target server through a SOCKS5 proxy.
pub async fn bind(
    remote: SocketAddrV4,
    options: &SocksOption,
) -> io::Result<(SocksRecvHalf, SocksSendHalf, u16)> {
    // Connect
    let stream = TcpStream::connect(remote).await?;
    let stream = BufStream::new(stream);

    let local = SocketAddrV4::new(Ipv4Addr::UNSPECIFIED, 0);
    let socket = UdpSocket::bind(local).await?;
    let local_port = socket.local_addr().unwrap().port();
    let datagram = match async_socks5::SocksDatagram::associate::<SocketAddrV4>(
        stream,
        socket,
        options.auth(),
        None,
    )
    .await
    {
        Ok(datagram) => datagram,
        Err(e) => return match e {
            async_socks5::Error::Io(e) => Err(e),
            _ => Err(io::Error::new(io::ErrorKind::Other, e)),
        },
    };

    let proxy_addr = match datagram.proxy_addr().clone() {
        AddrKind::Ip(proxy_addr) => proxy_addr,
        _ => unimplemented!(),
    };
    let (stream, socket) = datagram.into_inner();

    // Rewrite ASSOCIATE address
    let is_rewrite = options.force_associate_remote
        || match proxy_addr {
            SocketAddr::V4(proxy_addr) => match options.force_associate_bind_addr {
                true => false,
                false => proxy_addr.ip().is_private(),
            },
            SocketAddr::V6(_) => match options.force_associate_bind_addr {
                true => panic!("IPv6 is not supported yet"),
                false => true,
            },
        };
    if is_rewrite {
        let next_proxy_addr = SocketAddrV4::new(*remote.ip(), proxy_addr.port());
        socket.connect(next_proxy_addr).await?;

        trace!(
            "rewrite ASSOCIATE address {} to {}",
            proxy_addr,
            next_proxy_addr
        );
    }

    let a_stream = Arc::new(stream);
    let a_stream_cloned = Arc::clone(&a_stream);

    let a_socket = Arc::new(socket);
    let a_socket_cloned = Arc::clone(&a_socket);

    Ok((
        SocksRecvHalf::new(a_stream, a_socket),
        SocksSendHalf::new(a_stream_cloned, a_socket_cloned),
        local_port,
    ))
}
