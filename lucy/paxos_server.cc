#include "paxos_server.h"

#include <chrono>

#include "glog/logging.h"

#include "proto_util.h"

PaxosServer::PaxosServer(const Cluster& cluster, replica_index_t replica_index,
                         Object* object, Loop* loop)
    : Server(cluster, replica_index, object, loop) {
  if (AmLeader()) {
    LOG(INFO) << "PaxosServer leader listening on "
              << cluster_.UdpAddrs()[replica_index_] << ".";
    const std::chrono::milliseconds delay(100);
    resend_prepares_timer_ =
        loop->RegisterTimer(delay, [this]() { LeaderResendPrepares(); });
    resend_prepares_timer_.Start();
  } else {
    LOG(INFO) << "PaxosServer follower listening on "
              << cluster_.UdpAddrs()[replica_index_] << ".";
  }
}

void PaxosServer::Close() {
  Server::Close();
  if (AmLeader()) {
    resend_prepares_timer_.Close();
  }
}

void PaxosServer::OnRecv(const std::string& msg, const UdpAddress& src_addr) {
  if (AmLeader()) {
    OnRecvLeader(msg, src_addr);
  } else {
    OnRecvFollower(msg, src_addr);
  }
}

bool PaxosServer::AmLeader() const { return replica_index_ == 0; }

void PaxosServer::OnRecvLeader(const std::string& msg,
                               const UdpAddress& src_addr) {
  const auto proto = ProtoFromString<ServerMessage>(msg);
  if (proto.has_txn_request()) {
    HandleTxnRequest(proto.txn_request(), src_addr);
  } else if (proto.has_prepare_ok()) {
    HandlePrepareOk(proto.prepare_ok(), src_addr);
  } else {
    LOG(FATAL) << "Unexpected server message type";
  }
}

void PaxosServer::OnRecvFollower(const std::string& msg,
                                 const UdpAddress& src_addr) {
  const auto proto = ProtoFromString<ServerMessage>(msg);
  if (proto.has_prepare()) {
    HandlePrepare(proto.prepare(), src_addr);
  } else {
    LOG(FATAL) << "Unexpected server message type";
  }
}

void PaxosServer::HandleTxnRequest(const TxnRequest& txn_request,
                                   const UdpAddress& src_addr) {
  VLOG(1) << "PaxosServer received TxnRequest from " << src_addr << ".";

  // Drop this request if we're already waiting for too many requests.
  if (waiting_for_prepare_oks_.size() > 100) {
    VLOG(1) << "PaxosServer request buffer is full and is dropping a request.";
    return;
  }

  // Assign this transaction a new transaction index.
  const txn_index_t txn_index = txn_index_;
  txn_index_++;

  // Store the transaction for later. Once we have PrepareOk messages from all
  // the other servers and once we've committed all previous transactions, we
  // will commit this transaction.
  waiting_for_prepare_oks_.insert({txn_index, {txn_request, src_addr}});
  prepare_ok_replies_[txn_index];

  // Send Prepare messages to all the other servers.
  ServerMessage msg;
  msg.mutable_prepare()->set_txn_index(txn_index);
  msg.mutable_prepare()->set_txn(txn_request.txn());
  msg.mutable_prepare()->set_num_committed(num_committed_);
  const std::string msg_str = ProtoToString(msg);
  for (std::size_t i = 1; i < cluster_.Size(); ++i) {
    SendTo(msg_str, cluster_.UdpAddrs()[i]);
  }
}

void PaxosServer::HandlePrepareOk(const PrepareOk& prepare_ok,
                                  const UdpAddress& src_addr) {
  VLOG(1) << "PaxosServer received PrepareOk from " << src_addr
          << " for transaction " << prepare_ok.txn_index() << ".";

  // Save ourselves some typing.
  const txn_index_t txn_index = prepare_ok.txn_index();
  const replica_index_t replica_index = prepare_ok.replica_index();

  // Make sure we're expecting a PrepareOk message.
  if (waiting_for_prepare_oks_.find(txn_index) ==
      waiting_for_prepare_oks_.end()) {
    VLOG(1) << "PaxosServer leader received a PrepareOk for transaction "
            << txn_index << " but was not expecting PrepareOks. The leader "
                            "is ignoring this PrepareOk.";
    return;
  }

  // Record this PrepareOk.
  prepare_ok_replies_[txn_index].insert(replica_index);

  // If we haven't received a PrepareOk from every other server, then we're not
  // yet ready to commit the transaction.
  if (prepare_ok_replies_[txn_index].size() < cluster_.Size() - 1) {
    return;
  }

  VLOG(1) << "PaxosServer leader received a PrepareOk for transaction "
          << txn_index << " from all other replicas!";

  // Reply to the client. We should be waiting to commit the transaction first,
  // but this hack simulates a much more optimized variant of Paxos.
  ServerMessage msg;
  msg.mutable_txn_reply()->set_request_id(
      waiting_for_prepare_oks_[txn_index].txn_request.request_id());
  msg.mutable_txn_reply()->set_reply(
      object_->ExecTxn(waiting_for_prepare_oks_[txn_index].txn_request.txn()));
  SendTo(msg, waiting_for_prepare_oks_[txn_index].src_addr);

  // If we have received a PrepareOk from every other server, then we're ready
  // to try and commit this transaction. We add it to waiting_for_commit_ and
  // also clean up the metadata in prepare_ok_replies_ and
  // waiting_for_prepare_oks_.
  waiting_for_commit_.insert({txn_index, waiting_for_prepare_oks_[txn_index]});
  prepare_ok_replies_.erase(txn_index);
  waiting_for_prepare_oks_.erase(txn_index);
  LeaderCommitReadyTransactions();
}

void PaxosServer::HandlePrepare(const Prepare& prepare,
                                const UdpAddress& src_addr) {
  VLOG(1) << "PaxosServer received Prepare from " << src_addr
          << " for transaction " << prepare.txn_index() << ".";

  // Record the transaction and reply to the leader.
  pending_txns_[prepare.txn_index()] = prepare.txn();
  ServerMessage msg;
  msg.mutable_prepare_ok()->set_txn_index(prepare.txn_index());
  msg.mutable_prepare_ok()->set_replica_index(replica_index_);
  SendTo(msg, src_addr);

  // Commit any transactions that are ready to commit.
  num_committed_by_leader_ =
      std::max(num_committed_by_leader_, prepare.num_committed());
  FollowerCommitReadyTransactions();
}

void PaxosServer::LeaderCommitReadyTransactions() {
  VLOG(1) << "PaxosServer has " << num_committed_
          << " committed transactions and the first waiting for commit "
             "transaction is "
          << waiting_for_commit_.begin()->first << ".";

  auto it = waiting_for_commit_.begin();
  while (it->first == num_committed_) {
    // TODO: Clean up.
    // // Execute the transaction, and send a reply to the client.
    // const PendingTxn& pending_txn = it->second;
    // ServerMessage msg;
    // msg.mutable_txn_reply()->set_request_id(
    //     pending_txn.txn_request.request_id());
    // msg.mutable_txn_reply()->set_reply(
    //     object_->ExecTxn(pending_txn.txn_request.txn()));
    // SendTo(msg, pending_txn.src_addr);

    num_committed_++;
    it = waiting_for_commit_.erase(it);
  }
}

void PaxosServer::LeaderResendPrepares() {
  for (const auto& p : prepare_ok_replies_) {
    const txn_index_t txn_index = p.first;
    const std::set<replica_index_t> replies = p.second;
    const PendingTxn& pending_txn = waiting_for_prepare_oks_[txn_index];

    VLOG(1) << "Resending prepares for transaction " << txn_index << ".";

    ServerMessage msg;
    msg.mutable_prepare()->set_txn_index(txn_index);
    msg.mutable_prepare()->set_txn(pending_txn.txn_request.txn());
    msg.mutable_prepare()->set_num_committed(num_committed_);
    const std::string msg_str = ProtoToString(msg);
    for (std::size_t i = 1; i < cluster_.Size(); ++i) {
      if (replies.count(i) == 0) {
        SendTo(msg_str, cluster_.UdpAddrs()[i]);
      }
    }
  }

  resend_prepares_timer_.Reset();
}

void PaxosServer::FollowerCommitReadyTransactions() {
  auto it = pending_txns_.begin();
  while (it->first == num_committed_by_follower_ &&
         it->first < num_committed_by_leader_) {
    object_->ExecTxn(it->second);
    num_committed_by_follower_++;
    it = pending_txns_.erase(it);
  }
}
