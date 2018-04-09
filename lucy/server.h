#ifndef SERVER_H_
#define SERVER_H_

#include <cstdint>

#include "cluster.h"
#include "object.h"
#include "udp.h"

using txn_index_t = std::uint64_t;
using replica_index_t = std::uint64_t;

class Server {
 public:
  Server(const Cluster& cluster, replica_index_t replica_index, Object* object);
  virtual void Run() = 0;

 protected:
  const Cluster cluster_;
  const replica_index_t replica_index_;
  Object* object_;
  UdpSocket socket_;
};

#endif  // SERVER_H_
