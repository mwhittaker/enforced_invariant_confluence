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
  return "./benchmark_master_repl <benchmark_server_cluster> "
         "<benchmark_client_cluster>";
}

std::string ReplUsage() {
  return "start <num_servers> <server type> bank_account\n"
         "start <num_servers> <server type> two_ints <segment length>\n"
         "kill\n"
         "bank_account <num_servers> <server type> <fraction_widthraw> "
         "<duration_in_milliseconds>\n"
         "two_ints <num_servers> <server type> <duration_in_milliseconds>\n";
}

ServerType StringToServerType(const std::string& server_type) {
  if (server_type == "gossip") {
    return GOSSIP;
  } else if (server_type == "segmented") {
    return SEGMENTED;
  } else if (server_type == "paxos") {
    return PAXOS;
  } else {
    LOG(FATAL) << "Unexpected server type " << server_type << ".";
  }
}

}  // namespace

int main(int argc, char* argv[]) {
  google::InitGoogleLogging(argv[0]);

  if (argc != 3) {
    std::cerr << Usage() << std::endl;
    return EXIT_FAILURE;
  }

  const std::string benchmark_server_cluster_filename = argv[1];
  const std::string benchmark_client_cluster_filename = argv[2];
  const Cluster benchmark_server_cluster(benchmark_server_cluster_filename);
  const Cluster benchmark_client_cluster(benchmark_client_cluster_filename);
  BenchmarkMaster master(benchmark_server_cluster, benchmark_client_cluster);

  std::string line;
  std::cout << "> " << std::flush;
  while (std::getline(std::cin, line)) {
    std::vector<std::string> words = Split(line);

    if (words.size() == 4 && words[0] == "start" &&
        words[3] == "bank_account") {
      const std::uint64_t num_servers = std::stoul(words[1]);
      const ServerType server_type = StringToServerType(words[2]);

      BenchmarkServerStartRequest start;
      start.set_num_servers(num_servers);
      start.set_server_type(server_type);
      start.mutable_bank_account();
      master.ServersStart(start);
    } else if (words.size() == 5 && words[0] == "start" &&
               words[3] == "two_ints") {
      const std::uint64_t num_servers = std::stoul(words[1]);
      const ServerType server_type = StringToServerType(words[2]);
      const std::uint64_t segment_length = std::stoul(words[4]);

      BenchmarkServerStartRequest start;
      start.set_num_servers(num_servers);
      start.set_server_type(server_type);
      start.mutable_two_ints()->set_segment_length(segment_length);
      master.ServersStart(start);
    } else if (words.size() == 1 && words[0] == "kill") {
      BenchmarkServerKillRequest kill;
      master.ServersKill(kill);
    } else if (words.size() == 5 && words[0] == "bank_account") {
      const std::uint64_t num_servers = std::stoul(words[1]);
      const ServerType server_type = StringToServerType(words[2]);
      const double fraction_withdraw = std::stod(words[3]);
      const std::uint64_t duration_in_milliseconds = std::stoul(words[4]);

      BenchmarkClientBankAccountRequest bank_account;
      bank_account.set_num_servers(num_servers);
      bank_account.set_server_type(server_type);
      bank_account.set_fraction_withdraw(fraction_withdraw);
      bank_account.set_duration_in_milliseconds(duration_in_milliseconds);
      double txns_per_s = master.ClientsBankAccount(bank_account);
      std::cout << txns_per_s << " txns per second." << std::endl;
    }

    else if (words.size() == 4 && words[0] == "two_ints") {
      const std::uint64_t num_servers = std::stoul(words[1]);
      const ServerType server_type = StringToServerType(words[2]);
      const std::uint64_t duration_in_milliseconds = std::stoul(words[3]);

      BenchmarkClientTwoIntsRequest two_ints;
      two_ints.set_num_servers(num_servers);
      two_ints.set_server_type(server_type);
      two_ints.set_duration_in_milliseconds(duration_in_milliseconds);
      double txns_per_s = master.ClientsTwoInts(two_ints);
      std::cout << txns_per_s << " txns per second." << std::endl;
    } else {
      std::cerr << ReplUsage() << std::endl;
    }

    std::cout << "> " << std::flush;
  }
}
