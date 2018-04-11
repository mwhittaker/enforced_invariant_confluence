#ifndef BENCHMARK_SERVER_H_
#define BENCHMARK_SERVER_H_

#include <thread>

#include "benchmark.pb.h"
#include "cluster.h"
#include "server.h"
#include "udp.h"

class BenchmarkServer {
 public:
  BenchmarkServer(const Cluster& benchmark_server_cluster,
                  const Cluster& server_cluster, replica_index_t index)
      : socket_(benchmark_server_cluster.UdpAddrs()[index]),
        benchmark_server_cluster_(benchmark_server_cluster),
        server_cluster_(server_cluster),
        index_(index) {}

  void Run();

 private:
  void HandleStartRequest(const BenchmarkServerStartRequest& start_request,
                          const UdpAddress& src_addr);
  void HandleKillRequest(const BenchmarkServerKillRequest& kill_request,
                         const UdpAddress& src_addr);
  void StartServer(const BenchmarkServerStartRequest& start_request);

  UdpSocket socket_;
  const Cluster benchmark_server_cluster_;
  const Cluster server_cluster_;
  const replica_index_t index_;
  std::thread server_thread_;
};

#endif  //  BENCHMARK_SERVER_H_
