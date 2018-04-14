#include <cstdlib>
#include <future>
#include <iostream>
#include <string>
#include <thread>
#include <vector>

#include "glog/logging.h"

#include "benchmark.pb.h"
#include "cluster.h"
#include "string_util.h"
#include "two_ints_client.h"

namespace {

std::string Usage() {
  return "./two_ints_client_repl <server_cluster_file> "
         "<paxos|segmented|gossip>";
}

std::string ReplUsage() { return "get | x | y"; }

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

std::string ResultToString(TwoIntsClient::Result result) {
  switch (result) {
    case TwoIntsClient::COMMITTED:
      return "committed";
    case TwoIntsClient::ABORTED:
      return "aborted";
    default:
      LOG(FATAL) << "Unexpected TwoIntsClient::Result.";
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
  TwoIntsClient client(server_type, server_cluster, &loop);
  std::thread loop_thread([&loop]() { loop.Run(); });

  std::string line;
  std::cout << "> " << std::flush;
  while (std::getline(std::cin, line)) {
    if (line == "get") {
      std::promise<std::pair<std::int64_t, std::int64_t>> promise;
      std::future<std::pair<std::int64_t, std::int64_t>> future =
          promise.get_future();
      client.Get(&promise);
      std::cout << "(" << future.get().first << ", " << future.get().second
                << ")" << std::endl;
    } else if (line == "x") {
      std::promise<TwoIntsClient::Result> promise;
      std::future<TwoIntsClient::Result> future = promise.get_future();
      client.IncrementX(&promise);
      std::cout << ResultToString(future.get()) << std::endl;
    } else if (line == "y") {
      std::promise<TwoIntsClient::Result> promise;
      std::future<TwoIntsClient::Result> future = promise.get_future();
      client.DecrementY(&promise);
      std::cout << ResultToString(future.get()) << std::endl;
    } else {
      std::cout << ReplUsage() << std::endl;
    }
    std::cout << "> " << std::flush;
  }

  loop.RunFromAnotherThread([&loop] { loop.Stop(); });
  loop_thread.join();
}
