#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

#include "glog/logging.h"

#include "bank_account_client.h"
#include "cluster.h"
#include "string_util.h"

namespace {

void Usage() {
  std::cerr << "./bank_account_client_main <cluster_file>" << std::endl;
  ;
}

void ReplUsage() {
  std::cout << "get | deposit <n> | withdraw <n>" << std::endl;
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

  if (argc != 2) {
    Usage();
    return EXIT_FAILURE;
  }

  const std::string cluster_filename = argv[1];
  Cluster cluster(cluster_filename);
  BankAccountClient client;

  std::string line;
  std::cout << "> " << std::flush;
  std::size_t replica_ = 0;
  while (std::getline(std::cin, line)) {
    std::vector<std::string> words = Split(line);
    const UdpAddress& dst_addr = cluster.UdpAddrs()[replica_];
    if (words.size() == 1 && words[0] == "get") {
      std::cout << client.Get(dst_addr) << std::endl;
    } else if (words.size() == 2 && words[0] == "deposit") {
      BankAccountClient::Result result =
          client.Deposit(std::stoi(words[1]), dst_addr);
      std::cout << ResultToString(result) << std::endl;
    } else if (words.size() == 2 && words[0] == "withdraw") {
      BankAccountClient::Result result =
          client.Withdraw(std::stoi(words[1]), dst_addr);
      std::cout << ResultToString(result) << std::endl;
    } else {
      ReplUsage();
    }

    replica_ = (replica_ + 1) % cluster.Size();
    std::cout << "> " << std::flush;
  }
}
