#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

#include "glog/logging.h"

#include "bank_account_client.h"
#include "benchmark.pb.h"
#include "cluster.h"
#include "string_util.h"

namespace {

std::string Usage() {
  return "./bank_account_client_repl <cluster_file> <paxos|segmented|gossip>";
}

std::string ReplUsage() { return "get | deposit <n> | withdraw <n>"; }

ServerType StringToServerType(const std::string& s) {
  if (s == "paxos") {
    return PAXOS;
  } else if (s == "segmented") {
    return SEGMENTED;
  } else if (s == "gossip") {
    return GOSSIP;
  } else {
    LOG(FATAL) << "Unexpected server type.";
  }
}

std::string ResultToString(BankAccountClient::Result result) {
  switch (result) {
    case BankAccountClient::COMMITTED:
      return "committed";
    case BankAccountClient::ABORTED:
      return "aborted";
    default:
      LOG(FATAL) << "Unexpected BankAccountClient::Result.";
  }
}

}  // namespace

int main(int argc, char* argv[]) {
  google::InitGoogleLogging(argv[0]);

  if (argc != 3) {
    std::cerr << Usage() << std::endl;
    return EXIT_FAILURE;
  }
  const std::string cluster_filename = argv[1];
  const ServerType server_type = StringToServerType(argv[2]);

  Cluster cluster(cluster_filename);
  BankAccountClient client(server_type, cluster);

  std::string line;
  std::cout << "> " << std::flush;
  while (std::getline(std::cin, line)) {
    std::vector<std::string> words = Split(line);
    if (words.size() == 1 && words[0] == "get") {
      std::cout << client.Get() << std::endl;
    } else if (words.size() == 2 && words[0] == "deposit") {
      BankAccountClient::Result result = client.Deposit(std::stoi(words[1]));
      std::cout << ResultToString(result) << std::endl;
    } else if (words.size() == 2 && words[0] == "withdraw") {
      BankAccountClient::Result result = client.Withdraw(std::stoi(words[1]));
      std::cout << ResultToString(result) << std::endl;
    } else {
      std::cout << ReplUsage() << std::endl;
    }
    std::cout << "> " << std::flush;
  }
}
