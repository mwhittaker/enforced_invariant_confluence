#include "server.h"

Server::Server(Cluster cluster, int index, Object* object)
    : cluster_(std::move(cluster)), index_(index), object_(object) {}
