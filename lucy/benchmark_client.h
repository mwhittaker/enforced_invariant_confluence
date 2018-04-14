#ifndef BENCHMARK_CLIENT_H_
#define BENCHMARK_CLIENT_H_

#include <chrono>
#include <functional>

#include "glog/logging.h"

#include "benchmark.pb.h"
#include "cluster.h"
#include "loop.h"
#include "server.h"
#include "udp.h"

class BenchmarkClient : Loop::Actor {
 public:
  BenchmarkClient(const Cluster& benchmark_client_cluster,
                  const Cluster& server_cluster, replica_index_t index,
                  Loop* loop)
      : Loop::Actor(loop),
        benchmark_client_cluster_(benchmark_client_cluster),
        server_cluster_(server_cluster),
        index_(index) {
    LOG(INFO) << "BenchmarkClient listening on "
              << benchmark_client_cluster_.UdpAddrs()[index_] << ".";
  }

 private:
  struct WorkloadResult {
    const std::uint64_t num_txns;
    const std::chrono::nanoseconds duration;
    const double txns_per_second;
  };

  void OnRecv(const std::string& msg, const UdpAddress& src_addr) override;
  void HandleBankAccount(const BenchmarkClientBankAccountRequest& bank_account,
                         const UdpAddress& src_addr);
  void HandleTwoInts(const BenchmarkClientTwoIntsRequest& two_ints,
                     const UdpAddress& src_addr);
  WorkloadResult ExecWorkloadFor(Loop* client_loop,
                                 std::chrono::milliseconds duration,
                                 std::function<void(void)> f) const;
  Cluster ServerSubCluster(std::size_t n) const;

  const Cluster benchmark_client_cluster_;
  const Cluster server_cluster_;
  replica_index_t index_;
};

#endif  // BENCHMARK_CLIENT_H_
