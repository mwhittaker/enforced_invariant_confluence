#ifndef CLUSTER_H_
#define CLUSTER_H_

#include <string>
#include <vector>

#include "cluster.pb.h"
#include "host_port.h"

class Cluster {
 public:
  Cluster(const std::string& filename);
  Cluster(const ClusterProto& proto);
  Cluster(std::vector<HostPort> servers);
  const std::vector<HostPort>& Servers() const;

 private:
  std::vector<HostPort> servers_;
};

#endif  //  CLUSTER_H_
