#include "benchmark_server.h"

#include <memory>
#include <vector>

#include "bank_account.h"
#include "gossip_server.h"
#include "host_port.h"
#include "paxos_server.h"
#include "proto_util.h"
#include "segmented_master_server.h"
#include "segmented_server.h"
#include "server.pb.h"
#include "two_ints.h"

void BenchmarkServer::OnRecv(const std::string& msg,
                             const UdpAddress& src_addr) {
  BenchmarkServerRequest proto;
  proto.ParseFromString(msg);
  if (proto.has_start()) {
    HandleStartRequest(proto.start(), src_addr);
  } else if (proto.has_kill()) {
    HandleKillRequest(proto.kill(), src_addr);
  } else {
    LOG(FATAL) << "Unexpected message type.";
  }
}

void BenchmarkServer::HandleStartRequest(
    const BenchmarkServerStartRequest& start, const UdpAddress& src_addr) {
  DLOG(INFO) << "Received StartRequest from " << src_addr << ".";

  // Sanity check start.
  CHECK_GE(start.num_servers(), 1);
  CHECK_LT(index_, start.num_servers());

  // Start the server.
  StartServer(start);

  // Send an ack.
  BenchmarkServerReply reply;
  reply.mutable_start()->set_index(index_);
  SendTo(reply, src_addr);
}

void BenchmarkServer::HandleKillRequest(const BenchmarkServerKillRequest& kill,
                                        const UdpAddress& src_addr) {
  DLOG(INFO) << "Received KillRequest from " << src_addr << ".";
  (void)kill;

  if (server_) {
    // Kill the server.
    VLOG(1) << "Closing the server.";
    server_->Close();
    VLOG(1) << "Freeing the server.";
    server_.reset();
  }

  if (object_) {
    VLOG(1) << "Freeing the object.";
    object_.reset();
  }

  VLOG(1) << "Everything killed.";

  // Send an ack.
  BenchmarkServerReply reply;
  reply.mutable_kill()->set_index(index_);
  SendTo(reply, src_addr);
}

void BenchmarkServer::StartServer(const BenchmarkServerStartRequest& start) {
  // Create a subcluster.
  const std::vector<HostPort> all_host_ports = server_cluster_.HostPorts();
  auto begin = all_host_ports.begin();
  auto end = all_host_ports.begin() + start.num_servers();
  const std::vector<HostPort> host_ports(begin, end);
  Cluster cluster(host_ports);

  // Create the object.
  if (start.has_two_ints()) {
    object_ =
        std::unique_ptr<Object>(new TwoInts(start.two_ints().segment_length()));
  } else if (start.has_bank_account()) {
    object_ = std::unique_ptr<Object>(new BankAccount(cluster.Size(), index_));
  } else {
    LOG(FATAL) << "Unexpected object type.";
  }

  // Create the server.
  switch (start.server_type()) {
    case PAXOS: {
      server_ = std::unique_ptr<Server>(
          new PaxosServer(cluster, index_, object_.get(), loop_));
      break;
    }
    case SEGMENTED: {
      server_ = std::unique_ptr<Server>(
          new SegmentedServer(cluster, index_, object_.get(), loop_));
      break;
    }
    case SEGMENTED_MASTER: {
      server_ = std::unique_ptr<Server>(
          new SegmentedMasterServer(cluster, index_, object_.get(), loop_));
      break;
    }
    case GOSSIP: {
      server_ = std::unique_ptr<Server>(
          new GossipServer(cluster, index_, object_.get(), loop_));
      break;
    }
    default: { LOG(FATAL) << "Unexpected server type."; }
  }
}
