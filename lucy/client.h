#ifndef CLIENT_H_
#define CLIENT_H_

#include <string>

#include "benchmark.pb.h"
#include "cluster.h"
#include "server.h"
#include "udp.h"

class Client {
 protected:
  Client(ServerType server_type, const Cluster& server_cluster)
      : server_type_(server_type), server_cluster_(server_cluster) {}

  std::string ExecTxn(const std::string& txn, const UdpAddress& dst_addr);
  UdpAddress GetServerAddress() const;

 private:
  UdpSocket socket_;
  const ServerType server_type_;
  const Cluster server_cluster_;
};

#endif  // CLIENT_H_
