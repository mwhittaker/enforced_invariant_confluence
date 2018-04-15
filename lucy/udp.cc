#include <cstring>
#include <string>

#include "glog/logging.h"

#include "udp.h"

namespace {

constexpr std::size_t MAX_MESSAGE_SIZE = 65536;

}  // namespace

UdpAddress::UdpAddress() {}

UdpAddress::UdpAddress(const struct sockaddr_in& addr) : addr_(addr) {}

UdpAddress::UdpAddress(const SockAddrIn& sockaddr_in) {
  addr_.sin_family = AF_INET;
  addr_.sin_port = sockaddr_in.port();
  addr_.sin_addr.s_addr = sockaddr_in.addr();
}

UdpAddress::UdpAddress(const HostPort& host_port) {
  const std::string node = host_port.Host();
  const std::string service = std::to_string(host_port.Port());
  struct addrinfo hints;
  hints.ai_flags = 0;
  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_DGRAM;
  hints.ai_protocol = 0;
  addr_ = GetAddrInfo(node.c_str(), service.c_str(), &hints);
}

const struct sockaddr* UdpAddress::SockAddr() const {
  return reinterpret_cast<const struct sockaddr*>(&addr_);
}

int UdpAddress::SockAddrLen() const { return sizeof(addr_); }

SockAddrIn UdpAddress::ToProto() const {
  SockAddrIn proto;
  proto.set_port(addr_.sin_port);
  proto.set_addr(addr_.sin_addr.s_addr);
  return proto;
}

struct sockaddr_in UdpAddress::GetAddrInfo(const char* node,
                                           const char* service,
                                           struct addrinfo* hints) {
  struct addrinfo* res;
  int status = getaddrinfo(node, service, hints, &res);
  CHECK_EQ(status, 0) << gai_strerror(status);
  CHECK_EQ(res->ai_family, AF_INET) << res->ai_family;
  struct sockaddr_in addr =
      *reinterpret_cast<struct sockaddr_in*>(res->ai_addr);
  freeaddrinfo(res);
  return addr;
}

UdpSocket::UdpSocket() {
  socket_ = socket(AF_INET, SOCK_DGRAM, /*protocol=*/0);
  CHECK_NE(socket_, -1) << std::strerror(errno);
  int n = 1;
  int status = setsockopt(socket_, SOL_SOCKET, SO_REUSEADDR,
                          reinterpret_cast<char*>(&n), sizeof(n));
  CHECK_NE(status, -1) << std::strerror(errno);
}

UdpSocket::UdpSocket(const UdpAddress& addr) : UdpSocket() {
  int status = bind(socket_, addr.SockAddr(), addr.SockAddrLen());
  CHECK_NE(status, -1) << std::strerror(errno);
}

void UdpSocket::SendTo(const std::string& msg, const UdpAddress& addr) {
  CHECK_LE(msg.size(), MAX_MESSAGE_SIZE) << msg.size();
  int num_sent = sendto(socket_, msg.c_str(), msg.size(), /*flags=*/0,
                        addr.SockAddr(), sizeof(struct sockaddr_in));
  CHECK_NE(num_sent, -1) << std::strerror(errno);
  CHECK_EQ(num_sent, msg.size()) << num_sent << ", " << msg.size();
}

void UdpSocket::RecvFrom(std::string* msg, UdpAddress* addr) {
  char buf[MAX_MESSAGE_SIZE];
  struct sockaddr_in src_addr;
  socklen_t addrlen = sizeof(src_addr);
  int num_recv =
      recvfrom(socket_, buf, MAX_MESSAGE_SIZE, /*flags=*/0,
               reinterpret_cast<struct sockaddr*>(&src_addr), &addrlen);
  CHECK_NE(num_recv, -1) << std::strerror(errno);
  *msg = std::string(buf, num_recv);
  if (addr != nullptr) {
    *addr = UdpAddress(src_addr);
  }
}
