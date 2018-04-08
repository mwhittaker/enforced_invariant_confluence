#ifndef SEGMENTED_SERVER_H_
#define SEGMENTED_SERVER_H_

#include "server.h"

class SegmentedServer : public Server {
 public:
  SegmentedServer(Cluster cluster, int index, Object* object)
      : Server(std::move(cluster), index, object) {}

  void Run() override;
};

#endif  // SEGMENTED_SERVER_H_
