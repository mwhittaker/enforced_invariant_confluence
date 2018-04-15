#ifndef BENCHMARK_MASTER_H_
#define BENCHMARK_MASTER_H_

#include <functional>
#include <map>

#include "glog/logging.h"

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
  double ClientsBankAccount(
      const BenchmarkClientBankAccountRequest& vary_withdraws);
  double ClientsTwoInts(const BenchmarkClientTwoIntsRequest& vary_segments);

 private:
  Cluster ClientsSubcluster(std::size_t num_servers) const;

  using reply_to_index_t = std::function<replica_index_t(const std::string&)>;
  void WaitForNReplies(std::size_t n, const reply_to_index_t& f);

  template <typename T>
  using reply_to_t = std::function<T(const std::string&)>;

  template <typename T>
  std::map<replica_index_t, T> CollectNReplies(std::size_t n,
                                               const reply_to_t<T>& f) {
    // Wait for replies.
    std::map<replica_index_t, T> replies;
    while (replies.size() < n) {
      std::string reply_str;
      socket_.RecvFrom(&reply_str, nullptr);
      T x = f(reply_str);
      replica_index_t index = x.index();
      using value_type = typename std::map<replica_index_t, T>::value_type;
      replies.insert(value_type{index, std::move(x)});
      LOG(INFO) << replies.size() << " / " << n << ": Received reply from "
                << index << ".";
    }
    return replies;
  }

  UdpSocket socket_;
  const Cluster benchmark_server_cluster_;
  const Cluster benchmark_client_cluster_;
};

#endif  // BENCHMARK_MASTER_H_
