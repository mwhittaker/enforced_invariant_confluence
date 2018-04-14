#ifndef PAXOS_SERVER_H_
#define PAXOS_SERVER_H_

#include <cstdint>
#include <map>
#include <set>

#include "glog/logging.h"

#include "server.h"
#include "server.pb.h"

class PaxosServer : public Server {
 public:
  PaxosServer(const Cluster& cluster, replica_index_t replica_index,
              Object* object, Loop* loop)
      : Server(cluster, replica_index, object, loop) {
    if (AmLeader()) {
      LOG(INFO) << "PaxosServer leader listening on "
                << cluster_.UdpAddrs()[replica_index_] << ".";
    } else {
      LOG(INFO) << "PaxosServer follower listening on "
                << cluster_.UdpAddrs()[replica_index_] << ".";
    }
  }

  void OnRecv(const std::string& msg, const UdpAddress& src_addr) override;

 private:
  bool AmLeader() const;
  void OnRecvLeader(const std::string& msg, const UdpAddress& src_addr);
  void OnRecvFollower(const std::string& msg, const UdpAddress& src_addr);
  void HandleTxnRequest(const TxnRequest& txn_request,
                        const UdpAddress& src_addr);
  void HandlePrepareOk(const PrepareOk& prepare_ok, const UdpAddress& src_addr);
  void HandlePrepare(const Prepare& prepare, const UdpAddress& src_addr);
  void LeaderCommitReadyTransactions();
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

  // Follower.
  std::map<txn_index_t, std::string> pending_txns_;
  std::size_t num_committed_by_leader_ = 0;
  std::size_t num_committed_by_follower_ = 0;
};

#endif  // PAXOS_SERVER_H_
