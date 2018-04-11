#ifndef BENCHMARK_CLIENT_H_
#define BENCHMARK_CLIENT_H_

#include "benchmark.pb.h"
#include "cluster.h"
#include "server.h"
#include "udp.h"

class BenchmarkClient {
 public:
  BenchmarkClient(const Cluster& benchmark_client_cluster,
                  const Cluster& server_cluster, replica_index_t index)
      : socket_(benchmark_client_cluster.UdpAddrs()[index]),
        benchmark_client_cluster_(benchmark_client_cluster),
        server_cluster_(server_cluster) {}

  void Run();

 private:
  void HandleVaryWithdraws(
      const BenchmarkClientVaryWithdrawsRequest& vary_withdraws,
      const UdpAddress& src_addr);
  void HandleVarySegments(
      const BenchmarkClientVarySegmentsRequest& vary_segments,
      const UdpAddress& src_addr);
  void HandleVaryNodes(const BenchmarkClientVaryNodesRequest& vary_nodes,
                       const UdpAddress& src_addr);

  UdpSocket socket_;
  const Cluster benchmark_client_cluster_;
  const Cluster server_cluster_;
  replica_index_t index_;
};

#endif  // BENCHMARK_CLIENT_H_