#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string>
#include <thread>

#include "glog/logging.h"

#include "benchmark.pb.h"
#include "benchmark_server.h"
#include "cluster.h"
#include "udp.h"

namespace {

std::string Usage() {
  return "./benchmark_server.cc "
         "<benchmark_server_cluster> "
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
  const std::string benchmark_server_cluster_filename = argv[1];
  const std::string server_cluster_filename = argv[2];
  const std::uint64_t index = std::stoul(argv[3]);

  Cluster benchmark_server_cluster(benchmark_server_cluster_filename);
  Cluster server_cluster(server_cluster_filename);
  BenchmarkServer benchmark_server(benchmark_server_cluster, server_cluster,
                                   index);
  benchmark_server.Run();
}
