#include "benchmark_client.h"

#include <chrono>
#include <future>
#include <thread>
#include <vector>

#include "bank_account_client.h"
#include "host_port.h"
#include "proto_util.h"
#include "rand_util.h"
#include "two_ints_client.h"

void BenchmarkClient::Run() {
  LOG(INFO) << "BenchmarkClient listening on "
            << benchmark_client_cluster_.UdpAddrs()[index_] << ".";

  while (true) {
    std::string msg;
    UdpAddress src_addr;
    socket_.RecvFrom(&msg, &src_addr);

    const auto proto = ProtoFromString<BenchmarkClientRequest>(msg);
    if (proto.has_bank_account()) {
      HandleBankAccount(proto.bank_account(), src_addr);
    } else if (proto.has_two_ints()) {
      HandleTwoInts(proto.two_ints(), src_addr);
    } else {
      LOG(FATAL) << "Unexpected benchmark client message type.";
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
  const Cluster cluster = ServerSubCluster(bank_account.num_servers());
  Loop client_loop;
  BankAccountClient client(bank_account.server_type(), cluster, &client_loop);
  auto duration = milliseconds(bank_account.duration_in_milliseconds());
  const WorkloadResult result = ExecWorkloadFor(&client_loop, duration, [&]() {
    std::promise<BankAccountClient::Result> promise;
    auto future = promise.get_future();
    if (RandomBool(bank_account.fraction_withdraw())) {
      client.Withdraw(/*amount=*/1, &promise);
    } else {
      client.Deposit(/*amount=*/1, &promise);
    }
    future.get();
  });

  // Respond to the master.
  BenchmarkClientReply reply;
  reply.mutable_bank_account()->set_index(index_);
  reply.mutable_bank_account()->set_num_txns(result.num_txns);
  reply.mutable_bank_account()->set_duration_in_nanoseconds(
      result.duration.count());
  reply.mutable_bank_account()->set_txns_per_second(result.txns_per_second);
  socket_.SendTo(ProtoToString(reply), src_addr);
}

void BenchmarkClient::HandleTwoInts(
    const BenchmarkClientTwoIntsRequest& two_ints, const UdpAddress& src_addr) {
  using namespace std::chrono;
  LOG(INFO) << "Received TwoInts request from " << src_addr << ".";

  // Sanity check request.
  CHECK_LE(1, two_ints.num_servers());
  CHECK_LE(two_ints.num_servers(), server_cluster_.Size());

  // Run workload.
  const Cluster cluster = ServerSubCluster(two_ints.num_servers());
  Loop client_loop;
  TwoIntsClient client(two_ints.server_type(), cluster, &client_loop);
  auto duration = milliseconds(two_ints.duration_in_milliseconds());
  const WorkloadResult result = ExecWorkloadFor(&client_loop, duration, [&]() {
    std::promise<TwoIntsClient::Result> promise;
    auto future = promise.get_future();
    if (RandomBool(0.5)) {
      client.IncrementX(&promise);
    } else {
      client.DecrementY(&promise);
    }
    future.get();
  });

  // Respond to the master.
  BenchmarkClientReply reply;
  reply.mutable_two_ints()->set_index(index_);
  reply.mutable_two_ints()->set_num_txns(result.num_txns);
  reply.mutable_two_ints()->set_duration_in_nanoseconds(
      result.duration.count());
  reply.mutable_two_ints()->set_txns_per_second(result.txns_per_second);
  socket_.SendTo(ProtoToString(reply), src_addr);
}

BenchmarkClient::WorkloadResult BenchmarkClient::ExecWorkloadFor(
    Loop* client_loop, std::chrono::milliseconds duration,
    std::function<void(void)> f) const {
  using namespace std::chrono;

  // Start client loop.
  std::thread client_loop_thread([client_loop]() { client_loop->Run(); });

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

  // Stop client loop.
  client_loop->RunFromAnotherThread([client_loop]() { client_loop->Stop(); });
  client_loop_thread.join();

  return {num_transactions, actual_duration, txns_per_s};
}

Cluster BenchmarkClient::ServerSubCluster(std::size_t n) const {
  const std::vector<HostPort> all_host_ports = server_cluster_.HostPorts();
  auto begin = all_host_ports.begin();
  auto end = all_host_ports.begin() + n;
  const std::vector<HostPort> host_ports(begin, end);
  return Cluster(host_ports);
}
