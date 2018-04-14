#include <cstdlib>
#include <future>
#include <iostream>
#include <string>
#include <thread>
#include <vector>

#include "glog/logging.h"

#include "bank_account_client.h"
#include "benchmark.pb.h"
#include "cluster.h"
#include "loop.h"
#include "string_util.h"

namespace {

std::string Usage() {
  return "./bank_account_client_repl <server_cluster_file> "
         "<paxos|segmented|gossip>";
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
  const std::string server_cluster_filename = argv[1];
  const ServerType server_type = StringToServerType(argv[2]);

  Cluster server_cluster(server_cluster_filename);
  Loop loop;
  BankAccountClient client(server_type, server_cluster, &loop);
  std::thread loop_thread([&loop]() { loop.Run(); });

  std::string line;
  std::cout << "> " << std::flush;
  while (std::getline(std::cin, line)) {
    std::vector<std::string> words = Split(line);
    if (words.size() == 1 && words[0] == "get") {
      std::promise<std::int64_t> promise;
      std::future<std::int64_t> future = promise.get_future();
      client.Get(&promise);
      std::cout << future.get() << std::endl;
    } else if (words.size() == 2 && words[0] == "deposit") {
      std::promise<BankAccountClient::Result> promise;
      std::future<BankAccountClient::Result> future = promise.get_future();
      int amount = std::stoi(words[1]);
      client.Deposit(amount, &promise);
      std::cout << ResultToString(future.get()) << std::endl;
    } else if (words.size() == 2 && words[0] == "withdraw") {
      std::promise<BankAccountClient::Result> promise;
      std::future<BankAccountClient::Result> future = promise.get_future();
      int amount = std::stoi(words[1]);
      client.Withdraw(amount, &promise);
      std::cout << ResultToString(future.get()) << std::endl;
    } else {
      std::cout << ReplUsage() << std::endl;
    }
    std::cout << "> " << std::flush;
  }

  loop.RunFromAnotherThread([&loop] { loop.Stop(); });
  loop_thread.join();
}
