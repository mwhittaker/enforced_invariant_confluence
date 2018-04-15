#include <cstdlib>
#include <fstream>
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
    case SEGMENTED_MASTER:
      return "segmented_master";
    case PAXOS:
      return "paxos";
    default: { LOG(FATAL) << "Unexpected server type."; }
  }
}

void VaryWithdraws(const std::size_t num_servers, BenchmarkMaster *master) {
  std::ofstream vary_withdraws_file("vary_withdraws.csv");

  for (ServerType server_type : {GOSSIP, SEGMENTED_MASTER, PAXOS}) {
    std::vector<double> fraction_withdraws = {0,   0.01, 0.025, 0.05,
                                              0.1, 0.2,  0.3,   0.4};
    for (double fraction_withdraw : fraction_withdraws) {
      LOG(INFO) << "=====================================================";
      LOG(INFO) << "server_type       = " << ServerTypeToString(server_type);
      LOG(INFO) << "fraction_withdraw = " << fraction_withdraw;

      // Start the servers.
      LOG(INFO) << "Starting servers.";
      BenchmarkServerStartRequest start;
      start.set_num_servers(num_servers);
      start.mutable_bank_account();
      start.set_server_type(server_type);
      master->ServersStart(start);

      // Run the workload.
      LOG(INFO) << "Starting workload.";
      BenchmarkClientBankAccountRequest bank_account;
      bank_account.set_num_servers(num_servers);
      bank_account.set_fraction_withdraw(fraction_withdraw);
      bank_account.set_duration_in_milliseconds(5000);
      bank_account.set_server_type(server_type);
      double total_txns_per_second = master->ClientsBankAccount(bank_account);

      // Print and save the workload.
      LOG(INFO) << "";
      LOG(INFO) << ServerTypeToString(server_type) << ", " << fraction_withdraw
                << ", " << total_txns_per_second << std::endl;
      LOG(INFO) << "";
      vary_withdraws_file << ServerTypeToString(server_type) << ", "
                          << fraction_withdraw << ", " << total_txns_per_second
                          << std::endl;

      // Kill the servers.
      LOG(INFO) << "Killing servers.";
      BenchmarkServerKillRequest kill;
      master->ServersKill(kill);

      LOG(INFO) << "=====================================================";
      LOG(INFO) << "";
    }
  }
}

void VarySegments(std::size_t num_servers, BenchmarkMaster *master) {
  std::ofstream vary_segments_file("vary_segments.csv");

  for (ServerType server_type : {GOSSIP, SEGMENTED_MASTER, PAXOS}) {
    std::vector<std::uint64_t> segment_lengths = {2, 3, 4, 5, 6, 7, 8, 9, 10};
    for (double segment_length : segment_lengths) {
      LOG(INFO) << "=====================================================";
      LOG(INFO) << "server_type    = " << ServerTypeToString(server_type);
      LOG(INFO) << "segment_length = " << segment_length;

      // Start the servers.
      LOG(INFO) << "Starting servers.";
      BenchmarkServerStartRequest start;
      start.set_num_servers(num_servers);
      start.mutable_two_ints()->set_segment_length(segment_length);
      start.set_server_type(server_type);
      master->ServersStart(start);

      // Run the workload.
      LOG(INFO) << "Starting workload.";
      BenchmarkClientTwoIntsRequest two_ints;
      two_ints.set_num_servers(num_servers);
      two_ints.set_duration_in_milliseconds(5000);
      two_ints.set_server_type(server_type);
      double total_txns_per_second = master->ClientsTwoInts(two_ints);

      // Print and save the workload.
      LOG(INFO) << "";
      LOG(INFO) << ServerTypeToString(server_type) << ", " << segment_length
                << ", " << total_txns_per_second << std::endl;
      LOG(INFO) << "";
      vary_segments_file << ServerTypeToString(server_type) << ", "
                         << segment_length << ", " << total_txns_per_second
                         << std::endl;

      // Kill the servers.
      LOG(INFO) << "Killing servers.";
      BenchmarkServerKillRequest kill;
      master->ServersKill(kill);

      LOG(INFO) << "=====================================================";
      LOG(INFO) << "";
    }
  }
}

void VaryNodes(const std::size_t total_num_servers, BenchmarkMaster *master) {
  std::ofstream vary_nodes_file("vary_nodes.csv");

  for (ServerType server_type : {GOSSIP, SEGMENTED_MASTER, PAXOS}) {
    std::vector<std::uint64_t> num_servers = {2, 3, 4, 8, 16, 24, 32};
    for (double num_server : num_servers) {
      if (num_server > total_num_servers) {
        continue;
      }

      LOG(INFO) << "=====================================================";
      LOG(INFO) << "server_type = " << ServerTypeToString(server_type);
      LOG(INFO) << "num_server  = " << num_server;

      // Start the servers.
      LOG(INFO) << "Starting servers.";
      BenchmarkServerStartRequest start;
      start.set_num_servers(num_server);
      start.mutable_bank_account();
      start.set_server_type(server_type);
      master->ServersStart(start);

      // Run the workload.
      LOG(INFO) << "Starting workload.";
      BenchmarkClientBankAccountRequest bank_account;
      bank_account.set_num_servers(num_server);
      bank_account.set_fraction_withdraw(0.25);
      bank_account.set_duration_in_milliseconds(5000);
      bank_account.set_server_type(server_type);
      double total_txns_per_second = master->ClientsBankAccount(bank_account);

      // Print and save the workload.
      LOG(INFO) << "";
      LOG(INFO) << ServerTypeToString(server_type) << ", " << num_server << ", "
                << total_txns_per_second << std::endl;
      LOG(INFO) << "";
      vary_nodes_file << ServerTypeToString(server_type) << ", " << num_server
                      << ", " << total_txns_per_second << std::endl;

      // Kill the servers.
      LOG(INFO) << "Killing servers.";
      BenchmarkServerKillRequest kill;
      master->ServersKill(kill);

      LOG(INFO) << "=====================================================";
      LOG(INFO) << "";
    }
  }
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
    VarySegments(benchmark_server_cluster.Size(), &master);
  } else if (workload == "vary_nodes") {
    VaryNodes(benchmark_server_cluster.Size(), &master);
  } else {
    std::cerr << Usage() << std::endl;
    return EXIT_FAILURE;
  }
}
