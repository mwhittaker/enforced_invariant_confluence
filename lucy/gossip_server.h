#ifndef PAXOS_SERVER_H_
#define PAXOS_SERVER_H_

#include "server.h"

class GossipServer : public Server {
 public:
  GossipServer(Cluster cluster, int index, Object* object)
      : Server(std::move(cluster), index, object) {}

  void Run() override;
};

#endif  // PAXOS_SERVER_H_
