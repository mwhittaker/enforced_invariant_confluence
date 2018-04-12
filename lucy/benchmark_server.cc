#include "benchmark_server.h"

#include <memory>
#include <vector>

#include "glog/logging.h"

#include "bank_account.h"
#include "gossip_server.h"
#include "host_port.h"
#include "paxos_server.h"
#include "proto_util.h"
#include "segmented_server.h"
#include "server.pb.h"
#include "two_ints.h"

void BenchmarkServer::Run() {
  LOG(INFO) << "BenchmarkServer running on "
            << benchmark_server_cluster_.UdpAddrs()[index_] << ".";

  while (true) {
    std::string msg;
    UdpAddress src_addr;
    socket_.RecvFrom(&msg, &src_addr);

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
}

void BenchmarkServer::HandleStartRequest(
    const BenchmarkServerStartRequest& start, const UdpAddress& src_addr) {
  DLOG(INFO) << "Received StartRequest from " << src_addr << ".";

  // Sanity check start.
  CHECK_GE(start.num_servers(), 1);
  CHECK_LT(index_, start.num_servers());
  CHECK(!server_thread_.joinable());

  // Start the server.
  server_thread_ = std::thread(&BenchmarkServer::StartServer, this, start);

  // Send an ack.
  BenchmarkServerReply reply;
  reply.mutable_start()->set_index(index_);
  socket_.SendTo(ProtoToString(reply), src_addr);
}

void BenchmarkServer::HandleKillRequest(const BenchmarkServerKillRequest& kill,
                                        const UdpAddress& src_addr) {
  DLOG(INFO) << "Received KillRequest from " << src_addr << ".";
  (void)kill;

  if (server_thread_.joinable()) {
    // Send kill message to server.
    ServerMessage die;
    die.mutable_die();
    socket_.SendTo(ProtoToString(die), server_cluster_.UdpAddrs()[index_]);

    // Join the thread.
    server_thread_.join();
  }

  // Send an ack.
  BenchmarkServerReply reply;
  reply.mutable_kill()->set_index(index_);
  socket_.SendTo(ProtoToString(reply), src_addr);
}

void BenchmarkServer::StartServer(const BenchmarkServerStartRequest& start) {
  // Create a subcluster.
  const std::vector<HostPort> all_host_ports = server_cluster_.HostPorts();
  auto begin = all_host_ports.begin();
  auto end = all_host_ports.begin() + start.num_servers();
  const std::vector<HostPort> host_ports(begin, end);
  Cluster cluster(host_ports);

  // Create the object.
  std::unique_ptr<Object> object;
  switch (start.object()) {
    case BenchmarkServerStartRequest::TWO_INTS: {
      LOG(FATAL) << "TODO: Implement.";
      break;
    }
    case BenchmarkServerStartRequest::BANK_ACCOUNT: {
      object = std::unique_ptr<Object>(new BankAccount(cluster.Size(), index_));
      break;
    }
    default: { LOG(FATAL) << "Unexpected object type."; }
  }

  // Create the server.
  std::unique_ptr<Server> server;
  switch (start.server_type()) {
    case PAXOS: {
      server = std::unique_ptr<Server>(
          new PaxosServer(cluster, index_, object.get()));
      break;
    }
    case SEGMENTED: {
      server = std::unique_ptr<Server>(
          new SegmentedServer(cluster, index_, object.get()));
      break;
    }
    case GOSSIP: {
      server = std::unique_ptr<Server>(
          new GossipServer(cluster, index_, object.get()));
      break;
    }
    default: { LOG(FATAL) << "Unexpected server type."; }
  }

  server->Run();
}
