#include "cluster.h"

#include "google/protobuf/io/zero_copy_stream_impl.h"
#include "google/protobuf/text_format.h"

#include <fstream>

Cluster::Cluster(const std::string& filename) {
  ClusterProto proto;
  std::ifstream file(filename);
  ::google::protobuf::io::IstreamInputStream stream(&file);
  ::google::protobuf::TextFormat::Parse(&stream, &proto);
  InitFromProto(proto);
}

Cluster::Cluster(const ClusterProto& proto) { InitFromProto(proto); }

Cluster::Cluster(std::vector<HostPort> host_ports)
    : host_ports_(std::move(host_ports)) {
  for (const HostPort& host_port : host_ports_) {
    udp_addrs_.push_back(UdpAddress(host_port));
  }
}

std::size_t Cluster::Size() const { return host_ports_.size(); }

const std::vector<HostPort>& Cluster::HostPorts() const { return host_ports_; }

const std::vector<UdpAddress>& Cluster::UdpAddrs() const { return udp_addrs_; }

void Cluster::InitFromProto(const ClusterProto& proto) {
  for (const HostPortProto& host_port_proto : proto.host_port()) {
    HostPort host_port(host_port_proto);
    host_ports_.push_back(host_port);
    udp_addrs_.push_back(UdpAddress(host_port));
  }
}
