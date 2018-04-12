#include "benchmark_client.h"

#include <chrono>
#include <vector>

#include "glog/logging.h"

#include "bank_account_client.h"
#include "host_port.h"
#include "rand_util.h"
#include "two_ints_client.h"

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
      case BenchmarkClientRequest::BANK_ACCOUNT: {
        CHECK(proto.has_bank_account());
        HandleBankAccount(proto.bank_account(), src_addr);
        break;
      }
      case BenchmarkClientRequest::TWO_INTS: {
        CHECK(proto.has_two_ints());
        HandleTwoInts(proto.two_ints(), src_addr);
        break;
      }
      default: { LOG(FATAL) << "Unexpected benchmark client message type."; }
    }
  }
}

void BenchmarkClient::HandleBankAccount(
    const BenchmarkClientBankAccountRequest& bank_account,
    const UdpAddress& src_addr) {
  using namespace std::chrono;
  LOG(INFO) << "Received BankAccount request from " << src_addr << ".";

  // Sanity check request.
  CHECK_LE(0, bank_account.fraction_withdraw());
  CHECK_LE(bank_account.fraction_withdraw(), 1);
  CHECK_LE(1, bank_account.num_servers());
  CHECK_LE(bank_account.num_servers(), server_cluster_.Size());

  // Run workload.
  BankAccountClient client;
  auto duration = milliseconds(bank_account.duration_in_milliseconds());
  const WorkloadResult result = ExecWorkloadFor(duration, [&]() {
    bool deposit = RandomBool(bank_account.fraction_withdraw());
    int dst_index = bank_account.server_type() == PAXOS
                        ? 0
                        : RandomInt(0, bank_account.num_servers());
    const UdpAddress& dst_addr = server_cluster_.UdpAddrs()[dst_index];

    if (deposit) {
      client.Deposit(/*amount=*/1, dst_addr);
    } else {
      client.Withdraw(/*amount=*/1, dst_addr);
    }
  });

  // Respond to the master.
  BenchmarkClientReply reply;
  reply.set_type(BenchmarkClientReply::BANK_ACCOUNT);
  reply.mutable_bank_account()->set_index(index_);
  reply.mutable_bank_account()->set_num_txns(result.num_txns);
  reply.mutable_bank_account()->set_duration_in_nanoseconds(
      result.duration.count());
  reply.mutable_bank_account()->set_txns_per_second(result.txns_per_second);
  std::string reply_str;
  reply.SerializeToString(&reply_str);
  socket_.SendTo(reply_str, src_addr);
}

void BenchmarkClient::HandleTwoInts(
    const BenchmarkClientTwoIntsRequest& two_ints, const UdpAddress& src_addr) {
  using namespace std::chrono;
  LOG(INFO) << "Received TwoInts request from " << src_addr << ".";

  // Sanity check request.
  CHECK_LE(1, two_ints.num_servers());
  CHECK_LE(two_ints.num_servers(), server_cluster_.Size());

  // Run workload.
  TwoIntsClient client;
  auto duration = milliseconds(two_ints.duration_in_milliseconds());
  const WorkloadResult result = ExecWorkloadFor(duration, [&]() {
    bool incr_x = RandomBool(0.5);
    int dst_index = two_ints.server_type() == PAXOS
                        ? 0
                        : RandomInt(0, two_ints.num_servers());
    const UdpAddress& dst_addr = server_cluster_.UdpAddrs()[dst_index];

    if (incr_x) {
      client.IncrementX(dst_addr);
    } else {
      client.DecrementY(dst_addr);
    }
  });

  // Respond to the master.
  BenchmarkClientReply reply;
  reply.set_type(BenchmarkClientReply::TWO_INTS);
  reply.mutable_two_ints()->set_index(index_);
  reply.mutable_two_ints()->set_num_txns(result.num_txns);
  reply.mutable_two_ints()->set_duration_in_nanoseconds(
      result.duration.count());
  reply.mutable_two_ints()->set_txns_per_second(result.txns_per_second);
  std::string reply_str;
  reply.SerializeToString(&reply_str);
  socket_.SendTo(reply_str, src_addr);
}

BenchmarkClient::WorkloadResult BenchmarkClient::ExecWorkloadFor(
    std::chrono::milliseconds duration, std::function<void(void)> f) const {
  using namespace std::chrono;

  // Record the start and anticipated start time.
  high_resolution_clock clock;
  auto start = clock.now();
  auto planned_stop = start + duration;

  std::size_t num_transactions = 0;
  while (clock.now() < planned_stop) {
    // Perform multiple transactions per iteration to avoid checking the time
    // too often.
    constexpr std::size_t num_txns_per_iteration = 10;
    for (std::size_t i = 0; i < num_txns_per_iteration; ++i) {
      f();
      num_transactions++;
    }
  }

  // Calculate the throughput.
  auto actual_stop = clock.now();
  auto actual_duration = duration_cast<nanoseconds>(actual_stop - start);
  double txns_per_ns =
      static_cast<double>(num_transactions) / actual_duration.count();
  double txns_per_s = txns_per_ns * 1e9;
  return {num_transactions, actual_duration, txns_per_s};
}
