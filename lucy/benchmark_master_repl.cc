#include <cstdlib>
#include <iostream>
#include <string>

#include "glog/logging.h"

#include "benchmark.pb.h"
#include "benchmark_master.h"
#include "cluster.h"
#include "string_util.h"

namespace {

std::string Usage() {
  return "./benchmark_master_repl <benchmark_servers_cluster> "
         "<benchmark_clients_cluster>";
}

std::string ReplUsage() {
  return "  start <num_servers> <object> <server>\n"
         "  kill\n"
         "  vary_withdraws <num_servers> <fraction_widthraw> "
         "<duration_in_milliseconds>";
}

}  // namespace

int main(int argc, char* argv[]) {
  google::InitGoogleLogging(argv[0]);

  if (argc != 3) {
    std::cerr << Usage() << std::endl;
    return EXIT_FAILURE;
  }

  const std::string benchmark_servers_cluster_filename = argv[1];
  const std::string benchmark_clients_cluster_filename = argv[2];
  const Cluster benchmark_servers_cluster(benchmark_servers_cluster_filename);
  const Cluster benchmark_clients_cluster(benchmark_clients_cluster_filename);
  BenchmarkMaster master(benchmark_servers_cluster, benchmark_clients_cluster);

  std::string line;
  std::cout << "> " << std::flush;
  while (std::getline(std::cin, line)) {
    std::vector<std::string> words = Split(line);

    if (words.size() == 4 && words[0] == "start") {
      const std::uint64_t num_servers = std::stoul(words[1]);

      BenchmarkServerStartRequest::Object object;
      if (words[2] == "two_ints") {
        object = BenchmarkServerStartRequest::TWO_INTS;
      } else if (words[2] == "bank_account") {
        object = BenchmarkServerStartRequest::BANK_ACCOUNT;
      } else {
        std::cout << ReplUsage() << std::endl;
        break;
      }

      BenchmarkServerStartRequest::Server server;
      if (words[3] == "gossip") {
        server = BenchmarkServerStartRequest::GOSSIP;
      } else if (words[3] == "segmented") {
        server = BenchmarkServerStartRequest::SEGMENTED;
      } else if (words[3] == "paxos") {
        server = BenchmarkServerStartRequest::PAXOS;
      } else {
        std::cout << ReplUsage() << std::endl;
        break;
      }

      BenchmarkServerStartRequest start;
      start.set_num_servers(num_servers);
      start.set_object(object);
      start.set_server(server);
      master.ServersStart(start);
    } else if (words.size() == 1 && words[0] == "kill") {
      BenchmarkServerKillRequest kill;
      master.ServersKill(kill);
    } else if (words.size() == 4 && words[0] == "vary_withdraws") {
      const std::uint64_t num_servers = std::stoul(words[1]);
      const double fraction_withdraw = std::stod(words[2]);
      const std::uint64_t duration_in_milliseconds = std::stoul(words[3]);
      BenchmarkClientVaryWithdrawsRequest vary_withdraws;
      vary_withdraws.set_num_servers(num_servers);
      vary_withdraws.set_fraction_withdraw(fraction_withdraw);
      vary_withdraws.set_duration_in_milliseconds(duration_in_milliseconds);
      master.ClientsVaryWithdraws(vary_withdraws);
    } else {
      std::cerr << ReplUsage() << std::endl;
    }

    std::cout << "> " << std::flush;
  }
}
