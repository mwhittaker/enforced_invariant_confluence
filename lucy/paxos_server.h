#ifndef PAXOS_SERVER_H_
#define PAXOS_SERVER_H_

#include <cstdint>
#include <map>
#include <set>

#include "server.h"
#include "server.pb.h"

class PaxosServer : public Server {
 public:
  PaxosServer(const Cluster& cluster, int index, Object* object)
      : Server(cluster, index, object), socket_(cluster.UdpAddrs()[index]) {}

  void Run() override;

 private:
  bool AmLeader() const;
  void RunLeader();
  void RunFollower();
  void HandleTxnRequest(const TxnRequest& txn_request,
                        const UdpAddress& src_addr);
  void HandlePrepareOk(const PrepareOk& prepare_ok, const UdpAddress& src_addr);
  void HandlePrepare(const Prepare& prepare, const UdpAddress& src_addr);
  void LeaderCommitReadyTransactions();
  void FollowerCommitReadyTransactions();

  // Both.
  UdpSocket socket_;

  // Leader.
  struct PendingTxn {
    TxnRequest txn_request;
    UdpAddress src_addr;
  };
  std::int64_t txn_index_ = 0;
  std::int64_t num_committed_ = 0;
  std::map<std::int64_t, PendingTxn> waiting_for_prepare_oks_;
  std::map<std::int64_t, std::set<int>> prepare_ok_replies_;
  std::map<std::int64_t, PendingTxn> waiting_for_commit_;

  // Follower.
  std::map<std::int64_t, std::string> pending_txns_;
  std::int64_t num_committed_by_leader_ = 0;
  std::int64_t num_committed_by_follower_ = 0;
};

#endif  // PAXOS_SERVER_H_
