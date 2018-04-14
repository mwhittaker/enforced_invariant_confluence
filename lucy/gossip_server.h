#ifndef GOSSIP_SERVER_H_
#define GOSSIP_SERVER_H_

#include "glog/logging.h"

#include "loop.h"
#include "server.h"
#include "server.pb.h"
#include "udp.h"

class GossipServer : public Server {
 public:
  GossipServer(const Cluster& cluster, replica_index_t replica_index,
               Object* object, Loop* loop)
      : Server(cluster, replica_index, object, loop) {
    LOG(INFO) << "GossipServer running on "
              << cluster_.UdpAddrs()[replica_index_] << ".";
  }

  void OnRecv(const std::string& msg, const UdpAddress& src_addr) override;

 private:
  void HandleMergeRequest(const MergeRequest& merge_request,
                          const UdpAddress& src_addr);
  void HandleTxnRequest(const TxnRequest& txn_request,
                        const UdpAddress& src_addr);

  std::size_t num_requests_serviced_ = 0;
  const std::size_t num_requests_per_gossip_ = 10;
};

#endif  // GOSSIP_SERVER_H_
