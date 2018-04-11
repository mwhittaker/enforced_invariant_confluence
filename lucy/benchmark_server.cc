#include "benchmark_server.h"

#include <memory>
#include <vector>

#include "glog/logging.h"

#include "bank_account.h"
#include "gossip_server.h"
#include "host_port.h"
#include "paxos_server.h"
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
    switch (proto.type()) {
      case BenchmarkServerRequest::START_REQUEST: {
        CHECK(proto.has_start_request());
        HandleStartRequest(proto.start_request(), src_addr);
        break;
      }
      case BenchmarkServerRequest::KILL_REQUEST: {
        CHECK(proto.has_kill_request());
        HandleKillRequest(proto.kill_request(), src_addr);
        break;
      }
      default: { LOG(FATAL) << "Unexpected message type."; }
    }
  }
}

void BenchmarkServer::HandleStartRequest(
    const BenchmarkServerStartRequest& start_request,
    const UdpAddress& src_addr) {
  DLOG(INFO) << "Received StartRequest from " << src_addr << ".";

  // Start the server.
  CHECK(!server_thread_.joinable());
  server_thread_ =
      std::thread(&BenchmarkServer::StartServer, this, start_request);

  // Send an ack.
  BenchmarkServerReply reply;
  reply.set_type(BenchmarkServerReply::START_REPLY);
  reply.mutable_start_reply()->set_replica_index(index_);
  std::string reply_str;
  reply.SerializeToString(&reply_str);
  socket_.SendTo(reply_str, src_addr);
}

void BenchmarkServer::HandleKillRequest(
    const BenchmarkServerKillRequest& kill_request,
    const UdpAddress& src_addr) {
  DLOG(INFO) << "Received KillRequest from " << src_addr << ".";
  (void)kill_request;

  // Send kill message to server.
  ServerMessage msg;
  msg.set_type(ServerMessage::DIE);
  msg.mutable_die();
  std::string msg_str;
  msg.SerializeToString(&msg_str);
  socket_.SendTo(msg_str, server_cluster_.UdpAddrs()[index_]);

  // Join the thread.
  server_thread_.join();
}

void BenchmarkServer::StartServer(
    const BenchmarkServerStartRequest& start_request) {
  // Create a subcluster.
  const std::vector<HostPort> all_host_ports = server_cluster_.HostPorts();
  auto begin = all_host_ports.begin();
  auto end = all_host_ports.begin() + start_request.num_servers();
  const std::vector<HostPort> host_ports(begin, end);
  Cluster cluster(host_ports);

  // Create the object.
  std::unique_ptr<Object> object;
  switch (start_request.object()) {
    case BenchmarkServerStartRequest::TWO_INTS: {
      LOG(FATAL) << "Unimplemented";
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
  switch (start_request.server()) {
    case BenchmarkServerStartRequest::PAXOS: {
      server = std::unique_ptr<Server>(
          new PaxosServer(cluster, index_, object.get()));
      break;
    }
    case BenchmarkServerStartRequest::SEGMENTED: {
      server = std::unique_ptr<Server>(
          new SegmentedServer(cluster, index_, object.get()));
      break;
    }
    case BenchmarkServerStartRequest::GOSSIP: {
      server = std::unique_ptr<Server>(
          new GossipServer(cluster, index_, object.get()));
      break;
    }
    default: { LOG(FATAL) << "Unexpected server type."; }
  }

  server->Run();
}
