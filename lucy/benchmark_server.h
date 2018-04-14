#ifndef BENCHMARK_SERVER_H_
#define BENCHMARK_SERVER_H_

#include <thread>

#include "glog/logging.h"

#include "benchmark.pb.h"
#include "cluster.h"
#include "loop.h"
#include "server.h"
#include "udp.h"

class BenchmarkServer : public Loop::Actor {
 public:
  BenchmarkServer(const Cluster& benchmark_server_cluster,
                  const Cluster& server_cluster, replica_index_t index,
                  Loop* loop)
      : Loop::Actor(benchmark_server_cluster.UdpAddrs()[index], loop),
        benchmark_server_cluster_(benchmark_server_cluster),
        server_cluster_(server_cluster),
        index_(index),
        loop_(loop) {
    LOG(INFO) << "BenchmarkServer running on "
              << benchmark_server_cluster_.UdpAddrs()[index_] << ".";
  }

  void OnRecv(const std::string& msg, const UdpAddress& src_addr) override;

 private:
  void HandleStartRequest(const BenchmarkServerStartRequest& start_request,
                          const UdpAddress& src_addr);
  void HandleKillRequest(const BenchmarkServerKillRequest& kill_request,
                         const UdpAddress& src_addr);
  void StartServer(const BenchmarkServerStartRequest& start_request);

  const Cluster benchmark_server_cluster_;
  const Cluster server_cluster_;
  const replica_index_t index_;
  Loop* loop_;

  std::unique_ptr<Object> object_;
  std::unique_ptr<Server> server_;
};

#endif  //  BENCHMARK_SERVER_H_
