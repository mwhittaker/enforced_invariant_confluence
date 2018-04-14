#include "server.h"

#include "glog/logging.h"

Server::Server(const Cluster& cluster, replica_index_t replica_index,
               Object* object, Loop* loop)
    : Loop::Actor(cluster.UdpAddrs()[replica_index], loop),
      cluster_(cluster),
      replica_index_(replica_index),
      object_(object) {}
