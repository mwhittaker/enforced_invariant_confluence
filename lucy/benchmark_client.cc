#include "benchmark_client.h"

#include <chrono>
#include <vector>

#include "glog/logging.h"

#include "bank_account_client.h"
#include "host_port.h"
#include "rand_util.h"

void BenchmarkClient::Run() {
  LOG(INFO) << "BenchmarkClient listening on "
            << benchmark_client_cluster_.UdpAddrs()[index_] << ".";

  while (true) {
    std::string msg;
    UdpAddress src_addr;
    socket_.RecvFrom(&msg, &src_addr);

    BenchmarkClientRequest proto;
    proto.ParseFromString(msg);
    switch (proto.type()) {
      case BenchmarkClientRequest::VARY_WITHDRAWS: {
        CHECK(proto.has_vary_withdraws());
        HandleVaryWithdraws(proto.vary_withdraws(), src_addr);
        break;
      }
      case BenchmarkClientRequest::VARY_SEGMENTS: {
        CHECK(proto.has_vary_segments());
        HandleVarySegments(proto.vary_segments(), src_addr);
        break;
      }
      case BenchmarkClientRequest::VARY_NODES: {
        CHECK(proto.has_vary_nodes());
        HandleVaryNodes(proto.vary_nodes(), src_addr);
        break;
      }
      default: { LOG(FATAL) << "Unexpected benchmark client message type."; }
    }
  }
}

void BenchmarkClient::HandleVaryWithdraws(
    const BenchmarkClientVaryWithdrawsRequest& vary_withdraws,
    const UdpAddress& src_addr) {
  using namespace std::chrono;
  LOG(INFO) << "Received VaryWithdraw request from " << src_addr << ".";

  // Sanity check request.
  CHECK(0 <= vary_withdraws.fraction_withdraw() &&
        vary_withdraws.fraction_withdraw() <= 1)
      << vary_withdraws.fraction_withdraw();
  CHECK(1 <= vary_withdraws.num_servers() &&
        vary_withdraws.num_servers() <= server_cluster_.Size())
      << vary_withdraws.num_servers();

  // Record the start and anticipated start time.
  high_resolution_clock clock;
  auto start = clock.now();
  auto planned_stop =
      start + milliseconds(vary_withdraws.duration_in_milliseconds());

  BankAccountClient client;
  std::size_t num_transactions = 0;
  while (clock.now() < planned_stop) {
    // Perform multiple transactions per iteration to avoid checking the time
    // too often.
    constexpr std::size_t num_txns_per_iteration = 10;
    for (std::size_t i = 0; i < num_txns_per_iteration; ++i) {
      bool deposit = RandomBool(vary_withdraws.fraction_withdraw());
      int dst_index = RandomInt(0, vary_withdraws.num_servers());
      const UdpAddress& dst_addr = server_cluster_.UdpAddrs()[dst_index];
      if (deposit) {
        client.Deposit(/*amount=*/1, dst_addr);
      } else {
        client.Withdraw(/*amount=*/1, dst_addr);
      }

      num_transactions++;
    }
  }

  // Calculate the throughput.
  auto actual_stop = clock.now();
  auto duration = duration_cast<nanoseconds>(actual_stop - planned_stop);
  double txns_per_ns = num_transactions / duration.count();
  double txns_per_s = txns_per_ns * 1e9;

  // Respond to the master.
  BenchmarkClientReply reply;
  reply.set_type(BenchmarkClientReply::VARY_WITHDRAWS);
  reply.mutable_vary_withdraws()->set_index(index_);
  reply.mutable_vary_withdraws()->set_txns_per_second(txns_per_s);
  std::string reply_str;
  reply.SerializeToString(&reply_str);
  socket_.SendTo(reply_str, src_addr);
}

void BenchmarkClient::HandleVarySegments(
    const BenchmarkClientVarySegmentsRequest& vary_segments,
    const UdpAddress& src_addr) {
  LOG(INFO) << "Received VarySegments request from " << src_addr << ".";
  LOG(FATAL) << "Not implemented.";
  (void)vary_segments;
}

void BenchmarkClient::HandleVaryNodes(
    const BenchmarkClientVaryNodesRequest& vary_nodes,
    const UdpAddress& src_addr) {
  LOG(INFO) << "Received VaryNodes request from " << src_addr << ".";
  LOG(FATAL) << "Not implemented.";
  (void)vary_nodes;
}
