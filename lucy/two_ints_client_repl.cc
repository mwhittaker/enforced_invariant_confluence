#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

#include "glog/logging.h"

#include "benchmark.pb.h"
#include "cluster.h"
#include "string_util.h"
#include "two_ints_client.h"

namespace {

std::string Usage() {
  return "./two_ints_client_repl <cluster_file> <paxos|segmented|gossip>";
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
  const std::string cluster_filename = argv[1];
  const ServerType server_type = StringToServerType(argv[2]);

  Cluster cluster(cluster_filename);
  TwoIntsClient client(server_type, cluster);

  std::string line;
  std::cout << "> " << std::flush;
  while (std::getline(std::cin, line)) {
    if (line == "get") {
      const std::pair<std::int64_t, std::int64_t> xy = client.Get();
      std::cout << "(" << xy.first << ", " << xy.second << ")" << std::endl;
    } else if (line == "x") {
      std::cout << ResultToString(client.IncrementX()) << std::endl;
    } else if (line == "y") {
      std::cout << ResultToString(client.DecrementY()) << std::endl;
    } else {
      std::cout << ReplUsage() << std::endl;
    }
    std::cout << "> " << std::flush;
  }
}
