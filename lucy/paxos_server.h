#ifndef PAXOS_SERVER_H_
#define PAXOS_SERVER_H_

#include "server.h"

class PaxosServer : public Server {
 public:
  PaxosServer(Cluster cluster, int index, Object* object)
      : Server(std::move(cluster), index, object) {}

  void Run() override;
};

#endif  // PAXOS_SERVER_H_
