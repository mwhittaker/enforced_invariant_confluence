#include "server.h"

Server::Server(const Cluster& cluster, replica_index_t replica_index,
               Object* object)
    : cluster_(cluster),
      replica_index_(replica_index),
      object_(object),
      socket_(cluster.UdpAddrs()[replica_index]) {}
