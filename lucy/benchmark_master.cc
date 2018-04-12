#include "benchmark_master.h"

#include <set>

#include "google/protobuf/message.h"

#include "proto_util.h"

void BenchmarkMaster::ServersStart(const BenchmarkServerStartRequest& start) {
  // Send requests.
  BenchmarkServerRequest request;
  *request.mutable_start() = start;
  const std::string request_str = ProtoToString(request);
  for (std::size_t i = 0; i < start.num_servers(); ++i) {
    socket_.SendTo(request_str, benchmark_server_cluster_.UdpAddrs()[i]);
  }

  // Wait for replies.
  WaitForNReplies(start.num_servers(), [](const std::string& reply_str) {
    const auto reply = ProtoFromString<BenchmarkServerReply>(reply_str);
    CHECK(reply.has_start());
    return reply.start().index();
  });
}

void BenchmarkMaster::ServersKill(const BenchmarkServerKillRequest& kill) {
  const std::size_t n = benchmark_server_cluster_.Size();

  // Send requests.
  BenchmarkServerRequest request;
  *request.mutable_kill() = kill;
  const std::string request_str = ProtoToString(request);
  for (std::size_t i = 0; i < n; ++i) {
    socket_.SendTo(request_str, benchmark_server_cluster_.UdpAddrs()[i]);
  }

  // Wait for replies.
  WaitForNReplies(n, [](const std::string& reply_str) {
    const auto reply = ProtoFromString<BenchmarkServerReply>(reply_str);
    CHECK(reply.has_kill());
    return reply.kill().index();
  });
}

double BenchmarkMaster::ClientsBankAccount(
    const BenchmarkClientBankAccountRequest& bank_account) {
  const std::size_t n = benchmark_client_cluster_.Size();

  // Send requests.
  BenchmarkClientRequest request;
  *request.mutable_bank_account() = bank_account;
  const std::string request_str = ProtoToString(request);
  for (std::size_t i = 0; i < n; ++i) {
    socket_.SendTo(request_str, benchmark_client_cluster_.UdpAddrs()[i]);
  }

  // Wait for replies.
  using Reply = BenchmarkClientBankAccountReply;
  const std::map<replica_index_t, Reply> replies =
      CollectNReplies<Reply>(n, [](const std::string& reply_str) -> Reply {
        const auto reply = ProtoFromString<BenchmarkClientReply>(reply_str);
        CHECK(reply.has_bank_account());
        return reply.bank_account();
      });

  // Compute total throughput.
  double total_throughput = 0;
  for (const auto& p : replies) {
    total_throughput += p.second.txns_per_second();
  }
  return total_throughput;
}

double BenchmarkMaster::ClientsTwoInts(
    const BenchmarkClientTwoIntsRequest& two_ints) {
  const std::size_t n = benchmark_client_cluster_.Size();

  // Send requests.
  BenchmarkClientRequest request;
  *request.mutable_two_ints() = two_ints;
  const std::string request_str = ProtoToString(request);
  for (std::size_t i = 0; i < n; ++i) {
    socket_.SendTo(request_str, benchmark_client_cluster_.UdpAddrs()[i]);
  }

  // Wait for replies.
  using Reply = BenchmarkClientTwoIntsReply;
  const std::map<replica_index_t, Reply> replies =
      CollectNReplies<Reply>(n, [](const std::string& reply_str) -> Reply {
        const auto reply = ProtoFromString<BenchmarkClientReply>(reply_str);
        CHECK(reply.has_two_ints());
        return reply.two_ints();
      });

  // Compute total throughput.
  double total_throughput = 0;
  for (const auto& p : replies) {
    total_throughput += p.second.txns_per_second();
  }
  return total_throughput;
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
