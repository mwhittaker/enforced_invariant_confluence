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
  return "start "
         "<num_servers> "
         "<object> "
         "<server type>\n"

         "kill\n"

         "vary_withdraws "
         "<num_servers> "
         "<fraction_widthraw> "
         "<duration_in_milliseconds> "
         "<server type>";
}

BenchmarkServerStartRequest::Object StringToObject(const std::string& object) {
  if (object == "two_ints") {
    return BenchmarkServerStartRequest::TWO_INTS;
  } else if (object == "bank_account") {
    return BenchmarkServerStartRequest::BANK_ACCOUNT;
  } else {
    LOG(FATAL) << "Unexpected object " << object << ".";
  }
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

    if (words.size() == 4 && words[0] == "start") {
      const std::uint64_t num_servers = std::stoul(words[1]);
      BenchmarkServerStartRequest::Object object = StringToObject(words[2]);
      ServerType server_type = StringToServerType(words[3]);

      BenchmarkServerStartRequest start;
      start.set_num_servers(num_servers);
      start.set_object(object);
      start.set_server_type(server_type);
      master.ServersStart(start);
    } else if (words.size() == 1 && words[0] == "kill") {
      BenchmarkServerKillRequest kill;
      master.ServersKill(kill);
    } else if (words.size() == 5 && words[0] == "vary_withdraws") {
      const std::uint64_t num_servers = std::stoul(words[1]);
      const double fraction_withdraw = std::stod(words[2]);
      const std::uint64_t duration_in_milliseconds = std::stoul(words[3]);
      ServerType server_type = StringToServerType(words[4]);

      BenchmarkClientVaryWithdrawsRequest vary_withdraws;
      vary_withdraws.set_num_servers(num_servers);
      vary_withdraws.set_fraction_withdraw(fraction_withdraw);
      vary_withdraws.set_duration_in_milliseconds(duration_in_milliseconds);
      vary_withdraws.set_server_type(server_type);
      double txns_per_s = master.ClientsVaryWithdraws(vary_withdraws);
      std::cout << txns_per_s << " txns per second." << std::endl;
    } else {
      std::cerr << ReplUsage() << std::endl;
    }

    std::cout << "> " << std::flush;
  }
}
