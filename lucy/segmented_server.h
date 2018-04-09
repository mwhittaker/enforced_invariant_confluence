#ifndef SEGMENTED_SERVER_H_
#define SEGMENTED_SERVER_H_

#include <cstdint>
#include <deque>
#include <map>
#include <memory>
#include <set>

#include "server.h"
#include "server.pb.h"

using epoch_t = std::uint64_t;

class SegmentedServer : public Server {
 public:
  SegmentedServer(const Cluster& cluster, replica_index_t replica_index,
                  Object* object)
      : Server(cluster, replica_index, object) {}

  void Run() override;

 private:
  enum Mode { NORMAL = 0, SYNCING_LEADER = 1, SYNCING_FOLLOWER = 2 };

  struct PendingTxn {
    TxnRequest txn;
    UdpAddress src_addr;
  };

  void HandleTxnRequest(const TxnRequest& txn_request,
                        const UdpAddress& src_addr);
  void HandleMergeRequest(const MergeRequest& merge_request,
                          const UdpAddress& src_addr);
  void HandleSyncRequest(const SyncRequest& sync_request,
                         const UdpAddress& src_addr);
  void HandleSyncReply(const SyncReply& sync_reply, const UdpAddress& src_addr);
  void HandleStart(const Start& start, const UdpAddress& src_addr);
  void ProcessBufferedTxns();
  void SendMergeRequest();

  Mode mode_ = NORMAL;
  epoch_t epoch_ = 0;
  std::unique_ptr<PendingTxn> pending_sync_txn_;
  std::map<replica_index_t, SyncReply> pending_sync_replies_;
  std::deque<PendingTxn> pending_txn_requests_;
  int num_requests_serviced_ = 0;
  const int num_requests_per_gossip_ = 10;
};

#endif  // SEGMENTED_SERVER_H_
