#include "paxos_server.h"

#include "glog/logging.h"

void PaxosServer::Run() {
  if (AmLeader()) {
    RunLeader();
  } else {
    RunFollower();
  }
  // TODO: Implement.
}

bool PaxosServer::AmLeader() const { return replica_index_ == 0; }

void PaxosServer::RunLeader() {
  LOG(INFO) << "PaxosServer leader listening on "
            << cluster_.UdpAddrs()[replica_index_] << ".";

  while (true) {
    std::string msg;
    UdpAddress src_addr;
    socket_.RecvFrom(&msg, &src_addr);

    ServerMessage proto;
    proto.ParseFromString(msg);
    switch (proto.type()) {
      case ServerMessage::TXN_REQUEST: {
        CHECK(proto.has_txn_request());
        HandleTxnRequest(proto.txn_request(), src_addr);
        break;
      }
      case ServerMessage::PREPARE_OK: {
        CHECK(proto.has_prepare_ok());
        HandlePrepareOk(proto.prepare_ok(), src_addr);
        break;
      }
      case ServerMessage::DIE: {
        CHECK(proto.has_die());
        return;
      }
      default: { LOG(FATAL) << "Unexpected server message type"; }
    }
  }
}

void PaxosServer::RunFollower() {
  LOG(INFO) << "PaxosServer follower listening on "
            << cluster_.UdpAddrs()[replica_index_] << ".";

  while (true) {
    std::string msg;
    UdpAddress src_addr;
    socket_.RecvFrom(&msg, &src_addr);

    ServerMessage proto;
    proto.ParseFromString(msg);
    switch (proto.type()) {
      case ServerMessage::PREPARE: {
        CHECK(proto.has_prepare());
        HandlePrepare(proto.prepare(), src_addr);
        break;
      }
      default: { LOG(FATAL) << "Unexpected server message type"; }
    }
  }
}

void PaxosServer::HandleTxnRequest(const TxnRequest& txn_request,
                                   const UdpAddress& src_addr) {
  VLOG(1) << "PaxosServer received TxnRequest from " << src_addr << ".";

  // Assign this transaction a new transaction index.
  const txn_index_t txn_index = txn_index_;
  txn_index_++;

  // Store the transaction for later. Once we have PrepareOk messages from all
  // the other servers and once we've committed all previous transactions, we
  // will commit this transaction.
  waiting_for_prepare_oks_.insert({txn_index, {txn_request, src_addr}});

  // Send Prepare messages to all the other servers.
  ServerMessage msg;
  msg.set_type(ServerMessage::PREPARE);
  msg.mutable_prepare()->set_txn_index(txn_index);
  msg.mutable_prepare()->set_txn(txn_request.txn());
  msg.mutable_prepare()->set_num_committed(num_committed_);
  std::string s;
  msg.SerializeToString(&s);
  for (std::size_t i = 1; i < cluster_.Size(); ++i) {
    socket_.SendTo(s, cluster_.UdpAddrs()[i]);
  }
}

void PaxosServer::HandlePrepareOk(const PrepareOk& prepare_ok,
                                  const UdpAddress& src_addr) {
  VLOG(1) << "PaxosServer received PrepareOk from " << src_addr << ".";

  // Save ourselves some typing.
  const txn_index_t txn_index = prepare_ok.txn_index();
  const replica_index_t replica_index = prepare_ok.replica_index();

  // Make sure we're expecting a PrepareOk message.
  if (waiting_for_prepare_oks_.find(txn_index) ==
      waiting_for_prepare_oks_.end()) {
    LOG(INFO) << "PaxosServer leader received a PrepareOk for transaction "
              << txn_index << " but was not expecting PrepareOks. The leader "
                              "is ignoring this PrepareOk.";
  }

  // Record this PrepareOk.
  prepare_ok_replies_[txn_index].insert(replica_index);

  // If we haven't received a PrepareOk from every other server, then we're not
  // yet ready to commit the transaction.
  if (prepare_ok_replies_[txn_index].size() < cluster_.Size() - 1) {
    return;
  }

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
  VLOG(1) << "PaxosServer received Prepare from " << src_addr << ".";

  // Record the transaction and reply to the leader.
  pending_txns_[prepare.txn_index()] = prepare.txn();
  ServerMessage msg;
  msg.set_type(ServerMessage::PREPARE_OK);
  msg.mutable_prepare_ok()->set_txn_index(prepare.txn_index());
  msg.mutable_prepare_ok()->set_replica_index(replica_index_);
  std::string s;
  msg.SerializeToString(&s);
  socket_.SendTo(s, src_addr);

  // Commit any transactions that are ready to commit.
  num_committed_by_leader_ =
      std::max(num_committed_by_leader_, prepare.num_committed());
  FollowerCommitReadyTransactions();
}

void PaxosServer::LeaderCommitReadyTransactions() {
  auto it = waiting_for_commit_.begin();
  while (it->first == num_committed_) {
    // Execute the transaction, and send a reply to the client.
    const PendingTxn& pending_txn = it->second;
    ServerMessage msg;
    msg.set_type(ServerMessage::TXN_REPLY);
    msg.mutable_txn_reply()->set_reply(
        object_->Run(pending_txn.txn_request.txn()));
    std::string s;
    msg.SerializeToString(&s);
    socket_.SendTo(s, pending_txn.src_addr);

    num_committed_++;
    it = waiting_for_commit_.erase(it);
  }
}

void PaxosServer::FollowerCommitReadyTransactions() {
  auto it = pending_txns_.begin();
  while (it->first == num_committed_by_follower_ &&
         it->first < num_committed_by_leader_) {
    object_->Run(it->second);
    num_committed_by_follower_++;
    it = pending_txns_.erase(it);
  }
}
