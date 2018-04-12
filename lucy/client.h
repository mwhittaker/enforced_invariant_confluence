#ifndef CLIENT_H_
#define CLIENT_H_

#include <string>

#include "udp.h"

class Client {
 protected:
  std::string ExecTxn(const std::string& txn, const UdpAddress& dst_addr);

 private:
  UdpSocket socket_;
};

#endif  // CLIENT_H_
