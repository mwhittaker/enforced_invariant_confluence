#ifndef UDP_H_
#define UDP_H_

#include <iostream>

#include "arpa/inet.h"
#include "netdb.h"
#include "netinet/in.h"
#include "sys/socket.h"
#include "sys/types.h"

#include "host_port.h"

class UdpAddress {
 public:
  UdpAddress();
  UdpAddress(const struct sockaddr_in& addr);
  UdpAddress(const HostPort& host_port);
  const struct sockaddr* SockAddr() const;
  int SockAddrLen() const;

  friend std::ostream& operator<<(std::ostream& out, const UdpAddress& addr) {
    char s[INET_ADDRSTRLEN];
    inet_ntop(AF_INET, &(addr.addr_.sin_addr), s, INET_ADDRSTRLEN);
    out << s << ":" << addr.addr_.sin_port;
    return out;
  }

 private:
  static struct sockaddr_in GetAddrInfo(const char* node, const char* service,
                                        struct addrinfo* hints);

  struct sockaddr_in addr_;
};

class UdpSocket {
 public:
  UdpSocket();
  UdpSocket(const UdpAddress& addr);
  void SendTo(const std::string& msg, const UdpAddress& addr);
  void RecvFrom(std::string* msg, UdpAddress* addr);

 private:
  int socket_;
};

#endif  //  UDP_H_
