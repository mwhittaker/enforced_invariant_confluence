#include "server.h"

Server::Server(const Cluster& cluster, int index, Object* object)
    : cluster_(cluster), index_(index), object_(object) {}
