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
        server_cluster_(server_cluster),
        index_(index) {}

  void Run();

 private:
  void HandleBankAccount(const BenchmarkClientBankAccountRequest& bank_account,
                         const UdpAddress& src_addr);
  void HandleTwoInts(const BenchmarkClientTwoIntsRequest& two_ints,
                     const UdpAddress& src_addr);

  UdpSocket socket_;
  const Cluster benchmark_client_cluster_;
  const Cluster server_cluster_;
  replica_index_t index_;
};

#endif  // BENCHMARK_CLIENT_H_
