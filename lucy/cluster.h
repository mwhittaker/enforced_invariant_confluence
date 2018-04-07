#ifndef CLUSTER_H_
#define CLUSTER_H_

#include <string>
#include <vector>

#include "cluster.pb.h"
#include "host_port.h"
#include "udp.h"

class Cluster {
 public:
  Cluster(const std::string& filename);
  Cluster(const ClusterProto& proto);
  Cluster(std::vector<HostPort> host_ports);

  std::size_t Size() const;
  const std::vector<HostPort>& HostPorts() const;
  const std::vector<UdpAddress>& UdpAddrs() const;

 private:
  void InitFromProto(const ClusterProto& proto);

  std::vector<HostPort> host_ports_;
  std::vector<UdpAddress> udp_addrs_;
};

#endif  //  CLUSTER_H_
