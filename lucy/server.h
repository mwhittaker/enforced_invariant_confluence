#ifndef SERVER_H_
#define SERVER_H_

#include "cluster.h"
#include "object.h"

class Server {
 public:
  Server(const Cluster& cluster, int index, Object* object);
  virtual void Run() = 0;

 protected:
  const Cluster cluster_;
  const int index_;
  Object* object_;
};

#endif  // SERVER_H_
