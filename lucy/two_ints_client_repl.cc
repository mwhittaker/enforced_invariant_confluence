#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

#include "glog/logging.h"

#include "cluster.h"
#include "string_util.h"
#include "two_ints_client.h"

namespace {

std::string Usage() {
  return "./two_ints_client_repl <cluster_file> <paxos|segmented|gossip>";
}

std::string ReplUsage() { return "get | x | y"; }

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
  const std::string server_mode = argv[2];
  if (!(server_mode == "paxos" || server_mode == "segmented" ||
        server_mode == "gossip")) {
    std::cerr << Usage() << std::endl;
    return EXIT_FAILURE;
  }

  Cluster cluster(cluster_filename);
  TwoIntsClient client;

  std::string line;
  std::cout << "> " << std::flush;
  std::size_t replica_ = 0;
  while (std::getline(std::cin, line)) {
    const UdpAddress& dst_addr = cluster.UdpAddrs()[replica_];

    if (line == "get") {
      const std::pair<std::int64_t, std::int64_t> xy = client.Get(dst_addr);
      std::cout << "(" << xy.first << ", " << xy.second << ")" << std::endl;
    } else if (line == "x") {
      std::cout << ResultToString(client.IncrementX(dst_addr)) << std::endl;
    } else if (line == "y") {
      std::cout << ResultToString(client.DecrementY(dst_addr)) << std::endl;
    } else {
      std::cout << ReplUsage() << std::endl;
      continue;
    }

    if (server_mode != "paxos") {
      replica_ = (replica_ + 1) % cluster.Size();
    }
    std::cout << "> " << std::flush;
  }
}
