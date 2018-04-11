#ifndef BENCHMARK_MASTER_H_
#define BENCHMARK_MASTER_H_

#include <functional>

#include "benchmark.pb.h"
#include "cluster.h"
#include "server.h"
#include "udp.h"

class BenchmarkMaster {
 public:
  BenchmarkMaster(const Cluster& benchmark_server_cluster,
                  const Cluster& benchmark_client_cluster)
      : benchmark_server_cluster_(benchmark_server_cluster),
        benchmark_client_cluster_(benchmark_client_cluster) {}

  void ServersStart(const BenchmarkServerStartRequest& start);
  void ServersKill(const BenchmarkServerKillRequest& kill);
  void ClientsVaryWithdraws(
      const BenchmarkClientVaryWithdrawsRequest& vary_withdraws);
  void ClientsVarySegments(
      const BenchmarkClientVarySegmentsRequest& vary_segments);
  void ClientsVaryNodes(const BenchmarkClientVaryNodesRequest& vary_nodes);

 private:
  using reply_to_index_t = std::function<replica_index_t(const std::string&)>;
  void WaitForNReplies(std::size_t n, const reply_to_index_t& f);

  UdpSocket socket_;
  const Cluster benchmark_server_cluster_;
  const Cluster benchmark_client_cluster_;
};

#endif  // BENCHMARK_MASTER_H_
