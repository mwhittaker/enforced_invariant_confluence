#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

#include "glog/logging.h"

#include "bank_account.h"
#include "benchmark.pb.h"
#include "benchmark_master.h"
#include "cluster.h"

namespace {

std::string Usage() {
  return "./benchmark_master_main <benchmark_server_cluster> "
         "<benchmark_client_cluster> "
         "<vary_withdraws|vary_segments|vary_nodes>";
}

std::string ServerTypeToString(ServerType server_type) {
  switch (server_type) {
    case GOSSIP:
      return "gossip";
    case SEGMENTED:
      return "segmented";
    case PAXOS:
      return "paxos";
    default: { LOG(FATAL) << "Unexpected server type."; }
  }
}

void VaryWithdraws(const std::size_t num_servers, BenchmarkMaster *master) {
  for (ServerType server_type : {GOSSIP, SEGMENTED, PAXOS}) {
    std::vector<double> fraction_withdraws = {0.1, 0.2, 0.3, 0.4, 0.5,
                                              0.6, 0.7, 0.8, 0.9, 1.0};
    for (double fraction_withdraw : fraction_withdraws) {
      LOG(INFO) << "server_type = " << ServerTypeToString(server_type);
      LOG(INFO) << "fraction_withdraw = " << fraction_withdraw;

      // Start the servers.
      LOG(INFO) << "Starting servers.";
      BenchmarkServerStartRequest start;
      start.set_num_servers(num_servers);
      start.mutable_bank_account();
      start.set_server_type(server_type);
      master->ServersStart(start);

      // Run and print the workload.
      LOG(INFO) << "Starting workload.";
      BenchmarkClientBankAccountRequest bank_account;
      bank_account.set_num_servers(num_servers);
      bank_account.set_fraction_withdraw(fraction_withdraw);
      bank_account.set_duration_in_milliseconds(100);
      bank_account.set_server_type(server_type);
      double total_txns_per_second = master->ClientsBankAccount(bank_account);
      std::cout << ServerTypeToString(server_type) << ", " << fraction_withdraw
                << ", " << total_txns_per_second << std::endl;

      // Kill the servers.
      LOG(INFO) << "Killing servers.";
      BenchmarkServerKillRequest kill;
      master->ServersKill(kill);
    }
  }
}

void VarySegments(BenchmarkMaster *master) {
  (void)master;
  LOG(FATAL) << "TODO: Implement.";
}

void VaryNodes(BenchmarkMaster *master) {
  (void)master;
  LOG(FATAL) << "TODO: Implement.";
}

}  // namespace

int main(int argc, char *argv[]) {
  google::InitGoogleLogging(argv[0]);

  if (argc != 4) {
    std::cerr << Usage() << std::endl;
    return EXIT_FAILURE;
  }
  const std::string benchmark_server_cluster_filename = argv[1];
  const std::string benchmark_client_cluster_filename = argv[2];
  const std::string workload = argv[3];

  const Cluster benchmark_server_cluster(benchmark_server_cluster_filename);
  const Cluster benchmark_client_cluster(benchmark_client_cluster_filename);
  BenchmarkMaster master(benchmark_server_cluster, benchmark_client_cluster);
  if (workload == "vary_withdraws") {
    VaryWithdraws(benchmark_server_cluster.Size(), &master);
  } else if (workload == "vary_segments") {
    VarySegments(&master);
  } else if (workload == "vary_nodes") {
    VaryNodes(&master);
  } else {
    std::cerr << Usage() << std::endl;
    return EXIT_FAILURE;
  }
}
