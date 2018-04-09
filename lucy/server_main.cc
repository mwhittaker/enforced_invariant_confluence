#include <cstdlib>
#include <iostream>
#include <memory>
#include <string>

#include "glog/logging.h"

#include "bank_account.h"
#include "cluster.h"
#include "gossip_server.h"
#include "object.h"
#include "paxos_server.h"
#include "segmented_server.h"
#include "server.h"
#include "two_ints.h"

namespace {

std::string Usage() {
  return "./server_main <cluster_file> <index> <two_ints|bank_account> "
         "<paxos|segmented|gossip>";
}

}  // namespace

int main(int argc, char* argv[]) {
  google::InitGoogleLogging(argv[0]);

  // Parse command line arguments.
  if (argc != 5) {
    std::cerr << Usage() << std::endl;
    return EXIT_FAILURE;
  }
  const std::string cluster_filename = argv[1];
  const int replica_index = std::atoi(argv[2]);
  const std::string object_name = argv[3];
  const std::string server_mode = argv[4];

  // Cluster.
  Cluster cluster(cluster_filename);

  // Object.
  std::unique_ptr<Object> object;
  if (object_name == "two_ints") {
    // TODO: Implement.
  } else if (object_name == "bank_account") {
    object =
        std::unique_ptr<Object>(new BankAccount(cluster.Size(), replica_index));
  } else {
    std::cerr << Usage() << std::endl;
    return EXIT_FAILURE;
  }

  // Server.
  std::unique_ptr<Server> server;
  if (server_mode == "paxos") {
    server = std::unique_ptr<Server>(
        new PaxosServer(cluster, replica_index, object.get()));
  } else if (server_mode == "segmented") {
    server = std::unique_ptr<Server>(
        new SegmentedServer(cluster, replica_index, object.get()));
  } else if (server_mode == "gossip") {
    server = std::unique_ptr<Server>(
        new GossipServer(cluster, replica_index, object.get()));
  } else {
    std::cerr << Usage() << std::endl;
    return EXIT_FAILURE;
  }

  server->Run();
}
