#ifndef PAXOS_SERVER_H_
#define PAXOS_SERVER_H_

#include <cstdint>
#include <map>
#include <set>

#include "loop.h"
#include "server.h"
#include "server.pb.h"

class PaxosServer : public Server {
 public:
  PaxosServer(const Cluster& cluster, replica_index_t replica_index,
              Object* object, Loop* loop);

  void Close() override;

 private:
  // Message handling.
  void OnRecv(const std::string& msg, const UdpAddress& src_addr) override;
  void OnRecvLeader(const std::string& msg, const UdpAddress& src_addr);
  void OnRecvFollower(const std::string& msg, const UdpAddress& src_addr);
  void HandleTxnRequest(const TxnRequest& txn_request,
                        const UdpAddress& src_addr);
  void HandlePrepareOk(const PrepareOk& prepare_ok, const UdpAddress& src_addr);
  void HandlePrepare(const Prepare& prepare, const UdpAddress& src_addr);

  // Helpers.
  bool AmLeader() const;
  void LeaderCommitReadyTransactions();
  void LeaderResendPrepares();
  void FollowerCommitReadyTransactions();

  // Leader.
  struct PendingTxn {
    TxnRequest txn_request;
    UdpAddress src_addr;
  };
  txn_index_t txn_index_ = 0;
  std::size_t num_committed_ = 0;
  std::map<txn_index_t, PendingTxn> waiting_for_prepare_oks_;
  std::map<txn_index_t, std::set<replica_index_t>> prepare_ok_replies_;
  std::map<txn_index_t, PendingTxn> waiting_for_commit_;
  Loop::Timer resend_prepares_timer_;

  // Follower.
  std::map<txn_index_t, std::string> pending_txns_;
  std::size_t num_committed_by_leader_ = 0;
  std::size_t num_committed_by_follower_ = 0;
};

#endif  // PAXOS_SERVER_H_
