#include "cluster.h"

#include "google/protobuf/io/zero_copy_stream_impl.h"
#include "google/protobuf/text_format.h"

#include <fstream>

Cluster::Cluster(const std::string& filename) {
  ClusterProto proto;
  std::ifstream file(filename);
  ::google::protobuf::io::IstreamInputStream stream(&file);
  ::google::protobuf::TextFormat::Parse(&stream, &proto);
  for (const HostPortProto& host_port : proto.host_port()) {
    servers_.push_back(HostPort(host_port));
  }
}

Cluster::Cluster(const ClusterProto& proto) {
  for (const HostPortProto& host_port : proto.host_port()) {
    servers_.push_back(HostPort(host_port));
  }
}

Cluster::Cluster(std::vector<HostPort> servers)
    : servers_(std::move(servers)) {}

const std::vector<HostPort>& Cluster::Servers() const { return servers_; }
