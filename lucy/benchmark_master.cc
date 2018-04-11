#include "benchmark_master.h"

#include <set>

#include "glog/logging.h"
#include "google/protobuf/message.h"

void BenchmarkMaster::ServersStart(const BenchmarkServerStartRequest& start) {
  // Send requests.
  std::string start_str;
  start.SerializeToString(&start_str);
  for (std::size_t i = 0; i < start.num_servers(); ++i) {
    socket_.SendTo(start_str, benchmark_servers_cluster_.UdpAddrs()[i]);
  }

  // Wait for replies.
  WaitForNReplies(start.num_servers(), [](const std::string& reply_str) {
    BenchmarkServerReply reply;
    reply.ParseFromString(reply_str);
    CHECK(reply.type() == BenchmarkServerReply::START_REPLY);
    CHECK(reply.has_start_reply());
    return reply.start_reply().index();
  });
}

void BenchmarkMaster::ServersKill(const BenchmarkServerKillRequest& kill) {
  const std::size_t n = benchmark_servers_cluster_.Size();

  // Send requests.
  std::string kill_str;
  kill.SerializeToString(&kill_str);
  for (std::size_t i = 0; i < n; ++i) {
    socket_.SendTo(kill_str, benchmark_servers_cluster_.UdpAddrs()[i]);
  }

  // Wait for replies.
  WaitForNReplies(n, [](const std::string& reply_str) {
    BenchmarkServerReply reply;
    reply.ParseFromString(reply_str);
    CHECK(reply.type() == BenchmarkServerReply::KILL_REPLY);
    CHECK(reply.has_kill_reply());
    return reply.kill_reply().index();
  });
}

void BenchmarkMaster::ClientsVaryWithdraws(
    const BenchmarkClientVaryWithdrawsRequest& vary_withdraws) {
  const std::size_t n = benchmark_clients_cluster_.Size();

  // Send requests.
  std::string vary_withdraws_str;
  vary_withdraws.SerializeToString(&vary_withdraws_str);
  for (std::size_t i = 0; i < n; ++i) {
    socket_.SendTo(vary_withdraws_str,
                   benchmark_servers_cluster_.UdpAddrs()[i]);
  }

  // Wait for replies.
  WaitForNReplies(n, [](const std::string& reply_str) {
    BenchmarkClientReply reply;
    reply.ParseFromString(reply_str);
    CHECK(reply.type() == BenchmarkClientReply::VARY_WITHDRAWS);
    CHECK(reply.has_vary_withdraws());
    return reply.vary_withdraws().index();
  });
}

void BenchmarkMaster::ClientsVarySegments(
    const BenchmarkClientVarySegmentsRequest& vary_segments) {
  const std::size_t n = benchmark_clients_cluster_.Size();

  // Send requests.
  std::string vary_segments_str;
  vary_segments.SerializeToString(&vary_segments_str);
  for (std::size_t i = 0; i < n; ++i) {
    socket_.SendTo(vary_segments_str, benchmark_servers_cluster_.UdpAddrs()[i]);
  }

  // Wait for replies.
  WaitForNReplies(n, [](const std::string& reply_str) {
    BenchmarkClientReply reply;
    reply.ParseFromString(reply_str);
    CHECK(reply.type() == BenchmarkClientReply::VARY_WITHDRAWS);
    CHECK(reply.has_vary_segments());
    return reply.vary_segments().index();
  });
}
void BenchmarkMaster::ClientsVaryNodes(
    const BenchmarkClientVaryNodesRequest& vary_nodes) {
  const std::size_t n = benchmark_clients_cluster_.Size();

  // Send requests.
  std::string vary_nodes_str;
  vary_nodes.SerializeToString(&vary_nodes_str);
  for (std::size_t i = 0; i < n; ++i) {
    socket_.SendTo(vary_nodes_str, benchmark_servers_cluster_.UdpAddrs()[i]);
  }

  // Wait for replies.
  WaitForNReplies(n, [](const std::string& reply_str) {
    BenchmarkClientReply reply;
    reply.ParseFromString(reply_str);
    CHECK(reply.type() == BenchmarkClientReply::VARY_NODES);
    CHECK(reply.has_vary_nodes());
    return reply.vary_nodes().index();
  });
}

void BenchmarkMaster::WaitForNReplies(std::size_t n,
                                      const reply_to_index_t& f) {
  // Wait for replies.
  std::set<replica_index_t> replies;
  while (replies.size() < n) {
    std::string reply_str;
    socket_.RecvFrom(&reply_str, nullptr);
    const replica_index_t index = f(reply_str);
    replies.insert(index);
    LOG(INFO) << replies.size() << " / " << n << ": Received reply from "
              << index << ".";
  }
}
