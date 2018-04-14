#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string>
#include <thread>

#include "glog/logging.h"

#include "benchmark.pb.h"
#include "benchmark_client.h"
#include "cluster.h"
#include "loop.h"
#include "udp.h"

namespace {

std::string Usage() {
  return "./benchmark_server_main "
         "<benchmark_client_cluster> "
         "<server_cluster> "
         "<index>";
}

}  // namespace

int main(int argc, char* argv[]) {
  google::InitGoogleLogging(argv[0]);

  if (argc != 4) {
    std::cerr << Usage() << std::endl;
    return EXIT_FAILURE;
  }
  const std::string benchmark_client_cluster_filename = argv[1];
  const std::string server_cluster_filename = argv[2];
  const std::uint64_t index = std::stoul(argv[3]);

  const Cluster benchmark_client_cluster(benchmark_client_cluster_filename);
  const Cluster server_cluster(server_cluster_filename);
  Loop loop;
  BenchmarkClient benchmark_client(benchmark_client_cluster, server_cluster,
                                   index, &loop);
  loop.Run();
}
