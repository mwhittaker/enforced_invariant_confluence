#ifndef PAXOS_SERVER_H_
#define PAXOS_SERVER_H_

#include "server.h"
#include "server.pb.h"
#include "udp.h"

class GossipServer : public Server {
 public:
  GossipServer(const Cluster& cluster, int index, Object* object)
      : Server(cluster, index, object), socket_(cluster.UdpAddrs()[index]) {}

  void Run() override;

 private:
  void HandleMergeRequest(const MergeRequest& merge_request,
                          const UdpAddress& src_addr);
  void HandleTxnRequest(const TxnRequest& txn_request,
                        const UdpAddress& src_addr);

  int num_requests_serviced_ = 0;
  const int num_requests_per_gossip_ = 10;
  UdpSocket socket_;
};

#endif  // PAXOS_SERVER_H_
