#include "segmented_server.h"

#include "glog/logging.h"

#include "object.h"
#include "proto_util.h"
#include "rand_util.h"

SegmentedServer::SegmentedServer(const Cluster& cluster,
                                 replica_index_t replica_index, Object* object,
                                 Loop* loop)
    : Server(cluster, replica_index, object, loop) {
  LOG(INFO) << "SegmentedServer listening on "
            << cluster_.UdpAddrs()[replica_index_] << ".";

  const std::chrono::milliseconds delay(100);
  resend_sync_request_timer_ =
      loop->RegisterTimer(delay, [this]() { ResendSyncRequest(); });
  resend_start_timer_ = loop->RegisterTimer(delay, [this]() { ResendStart(); });
}

void SegmentedServer::Close() {
  Server::Close();
  resend_sync_request_timer_.Close();
  resend_start_timer_.Close();
}

void SegmentedServer::OnRecv(const std::string& msg,
                             const UdpAddress& src_addr) {
  const auto proto = ProtoFromString<ServerMessage>(msg);
  if (proto.has_txn_request()) {
    HandleTxnRequest(proto.txn_request(), src_addr);
  } else if (proto.has_merge_request()) {
    HandleMergeRequest(proto.merge_request(), src_addr);
  } else if (proto.has_sync_request()) {
    HandleSyncRequest(proto.sync_request(), src_addr);
  } else if (proto.has_sync_reply()) {
    HandleSyncReply(proto.sync_reply(), src_addr);
  } else if (proto.has_start()) {
    HandleStart(proto.start(), src_addr);
  } else if (proto.has_start_ack()) {
    HandleStartAck(proto.start_ack(), src_addr);
  } else {
    LOG(FATAL) << "Unexpected server message type " << proto.GetTypeName()
               << " = " << proto.DebugString();
  }
}

void SegmentedServer::HandleTxnRequest(const TxnRequest& txn_request,
                                       const UdpAddress& src_addr) {
  VLOG(1) << "Received TxnRequest from " << src_addr << ".";

  // Buffer the request in pending_txn_requests_ if we have space. If we're in
  // normal mode, we'll execute it right away. If we're in sync mode, we'll
  // process requests in a FIFO order. If pending_txn_requests_ is too big,
  // then we just drop the request. The client will resend it later.
  if (pending_txn_requests_.size() <= 100) {
    pending_txn_requests_.push_back(PendingTxn{txn_request, src_addr});
  } else {
    VLOG(1)
        << "SegmentedServer request buffer is full and is dropping a request.";
  }

  if (mode_ != NORMAL) {
    VLOG(1) << "SegmentedServer received a transaction request during a "
               "sync. The request is begin buffered for later execution.";
  } else {
    ProcessBufferedTxns();
  }
}

void SegmentedServer::HandleMergeRequest(const MergeRequest& merge_request,
                                         const UdpAddress& src_addr) {
  CHECK(merge_request.has_epoch());
  VLOG(1) << "Received MergeRequest from " << src_addr << " with epoch "
          << merge_request.epoch() << ".";

  if (mode_ != NORMAL) {
    VLOG(1) << "SegmentedServer received a MergeRequest during a sync, so "
               "the SegmentedServer is ignoring the MergeRequest.";
    return;
  }

  CHECK_LE(merge_request.epoch(), epoch_);
  if (merge_request.epoch() == epoch_) {
    object_->Merge(merge_request.object());
  } else {
    VLOG(1) << "SegmentedServer received a MergeRequest for epoch "
            << merge_request.epoch()
            << " which is earlier than the current epoch " << epoch_
            << ", so the SegmentedServer is ignoring this MergeRequest";
  }
}

void SegmentedServer::HandleSyncRequest(const SyncRequest& sync_request,
                                        const UdpAddress& src_addr) {
  VLOG(1) << "Received SyncRequest from " << src_addr << " with epoch "
          << sync_request.epoch() << ".";

  if (sync_request.epoch() < epoch_) {
    VLOG(1) << "SegmentedServer received a SyncRequest for epoch "
            << sync_request.epoch()
            << " which is earlier than the current epoch " << epoch_
            << ", so the SegmentedServer is ignoring this SyncRequest";
    return;
  }

  if (mode_ == NORMAL) {
    if (sync_request.epoch() == epoch_) {
      VLOG(1)
          << "SegmentedServer in normal mode received a SyncRequest for epoch "
          << sync_request.epoch() << " which is equal to the current epoch "
          << epoch_ << ", so the SegmentedServer is ignoring this SyncRequest";
      return;
    }

    CHECK_EQ(sync_request.epoch(), epoch_ + 1);
    // Fall through and send reply.
  } else if (mode_ == SYNCING_FOLLOWER) {
    if (sync_request.epoch() > epoch_) {
      VLOG(1) << "SegmentedServer syncing follower in epoch " << epoch_
              << " received a sync request for epoch " << sync_request.epoch()
              << ". This means that the SegmentedServer hasn't yet received a "
                 "start for epoch "
              << epoch_ << ". The SegmentedServer is ignoring the request and "
                           "waiting for the missing start.";
      CHECK_EQ(sync_request.epoch(), epoch_ + 1);
      return;
    }

    CHECK_EQ(sync_request.epoch(), epoch_);
    // Fall through and send reply.
  } else if (mode_ == SYNCING_LEADER) {
    CHECK_EQ(sync_request.epoch(), epoch_);

    if (replica_index_ > sync_request.replica_index()) {
      VLOG(1) << "SegmentedServer in syncing leader mode received a "
                 "SyncRequest from replica "
              << sync_request.replica_index()
              << " which is less that the SegmentedServer's index  "
              << replica_index_
              << ", so the SegmentedServer is ignoring this SyncRequest";
      return;
    }

    // Rebuffer our pending sync transaction.
    VLOG(1) << "SegmentedServer in syncing leader mode received a "
               "SyncRequest from replica "
            << sync_request.replica_index()
            << " which is larger that the SegmentedServer's index  "
            << replica_index_
            << ", so the SegmentedServer is becoming a follower.";
    CHECK_GT(sync_request.replica_index(), replica_index_);
    CHECK(pending_sync_txn_);
    pending_txn_requests_.push_front(*pending_sync_txn_);
    pending_sync_txn_.reset();
    pending_sync_replies_.clear();
    resend_sync_request_timer_.Stop();

    // Fall through and send reply.
  } else {
    CHECK_EQ(mode_, WAITING_FOR_START_ACKS);

    if (sync_request.epoch() > epoch_) {
      VLOG(1) << "SegmentedServer waiting for acks in epoch " << epoch_
              << " received a sync request for epoch " << sync_request.epoch()
              << ". This means that the SegmentedServer sent starts to "
                 "everyone but is still waiting for a reply. In the meantime, "
                 "another replica is starting a sync for epoch "
              << epoch_ << ". The SegmentedServer is ignoring the request and "
                           "waiting for the missing start ack.";
      CHECK_EQ(sync_request.epoch(), epoch_ + 1);
      return;
    }

    CHECK_EQ(sync_request.epoch(), epoch_);
    VLOG(1) << "SegmentedServer waiting for acks in epoch " << epoch_
            << " received a sync request for epoch " << sync_request.epoch()
            << ". This server has already determined this epoch, so it is "
               "ignoring the request.";
    return;
  }

  mode_ = SYNCING_FOLLOWER;
  epoch_ = sync_request.epoch();

  ServerMessage msg;
  msg.mutable_sync_reply()->set_replica_index(replica_index_);
  msg.mutable_sync_reply()->set_epoch(sync_request.epoch());
  msg.mutable_sync_reply()->set_object(object_->Get());
  SendTo(msg, src_addr);
}

void SegmentedServer::HandleSyncReply(const SyncReply& sync_reply,
                                      const UdpAddress& src_addr) {
  VLOG(1) << "Received SyncReply from " << src_addr << " with epoch "
          << sync_reply.epoch() << ".";

  // We cannot receive a sync reply for a sync request with an epoch higher
  // than our own because if we ever sent such a request, we would have updated
  // our epoch.
  CHECK_LE(sync_reply.epoch(), epoch_);

  // Ignore old SyncReplies.
  if (sync_reply.epoch() < epoch_) {
    VLOG(1) << "SegmentedServer received a SyncReply for epoch "
            << sync_reply.epoch() << " which is earlier than the current epoch "
            << epoch_ << ", so the SegmentedServer is ignoring this SyncReply";
    return;
  }

  if (mode_ != SYNCING_LEADER) {
    VLOG(1) << "SegmentedServer received a SyncReply but it is not a syncing "
               "leader, so it is ignoring the SyncReply.";
    return;
  }

  CHECK_EQ(sync_reply.epoch(), epoch_);
  CHECK_EQ(mode_, SYNCING_LEADER);
  pending_sync_replies_.insert({sync_reply.replica_index(), sync_reply});
  if (pending_sync_replies_.size() < cluster_.Size() - 1) {
    // We haven't yet heard back from all the other replicas.
    return;
  }

  VLOG(1) << "SegmentedServer sync leader received sync replies from all "
             "other replicas.";

  // Merge the objects from all the other replicas.
  for (const std::pair<const replica_index_t, SyncReply>& p :
       pending_sync_replies_) {
    const SyncReply& sync_reply = p.second;
    object_->Merge(sync_reply.object());
  }

  // Execute the pending sync transaction and reply to the client.
  CHECK(pending_sync_txn_);
  std::string reply = object_->ExecTxn(pending_sync_txn_->txn.txn());
  ServerMessage txn_reply;

  txn_reply.mutable_txn_reply()->set_request_id(
      pending_sync_txn_->txn.request_id());
  txn_reply.mutable_txn_reply()->set_reply(reply);
  SendTo(txn_reply, pending_sync_txn_->src_addr);

  // Send Start messages to the other replicas.
  VLOG(1) << "SegmentedServer sync leader sending start to all other replicas.";
  ServerMessage start;
  start.mutable_start()->set_object(object_->Get());
  start.mutable_start()->set_epoch(epoch_);
  pending_start_ = start;
  const std::string start_s = ProtoToString(start);
  for (replica_index_t i = 0; i < cluster_.Size(); ++i) {
    if (i != replica_index_) {
      SendTo(start_s, cluster_.UdpAddrs()[i]);
    }
  }

  // Perform start.
  object_->Set(start.start().object());

  // Clean up our metadata and set up timers.
  mode_ = WAITING_FOR_START_ACKS;
  resend_sync_request_timer_.Stop();
  pending_sync_replies_.clear();
  pending_sync_txn_.reset();
  resend_start_timer_.Start();
}

void SegmentedServer::HandleStart(const Start& start,
                                  const UdpAddress& src_addr) {
  VLOG(1) << "Received Start from " << src_addr << " with epoch "
          << start.epoch() << ".";

  // This start has to be a lingering start from the past. If it were from the
  // present or the future, the replica that sent it would have to have
  // received a StartReply from us which means that we would have updated our
  // epoch to be at least as big as it, if not bigger.
  CHECK_LE(start.epoch(), epoch_);

  // If the start.epoch() is from the past, then we just ignore it. It is a
  // duplicated or re-ordered message.
  if (start.epoch() < epoch_) {
    VLOG(1) << "SegmentedServer received a Start for epoch " << start.epoch()
            << " which is earlier than the current epoch " << epoch_
            << ", so the SegmentedServer is ignoring this StartAck.";
    return;
  }

  CHECK_EQ(start.epoch(), epoch_);
  if (mode_ == NORMAL) {
    VLOG(1) << "SegmentedServer received a Start with epoch " << start.epoch()
            << " but is in normal mode in epoch " << epoch_
            << " so it must have already responded to this start request. It "
               "is replying with an ack again.";
    ServerMessage start_ack;
    start_ack.mutable_start_ack()->set_epoch(epoch_);
    start_ack.mutable_start_ack()->set_replica_index(replica_index_);
    SendTo(start_ack, src_addr);
    return;
  }

  // If the start epoch is the same as the current epoch, then we must be a
  // syncing follower. In order for the syncing leader to have sent the start,
  // it would have had to receive a SyncReply from us. When we sent the
  // SyncReply, we would have transitionined into SYNCING_FOLLOWER mode.
  CHECK_EQ(mode_, SYNCING_FOLLOWER);

  // Perform start.
  object_->Set(start.object());

  // Ack leader.
  ServerMessage start_ack;
  start_ack.mutable_start_ack()->set_epoch(epoch_);
  start_ack.mutable_start_ack()->set_replica_index(replica_index_);
  SendTo(start_ack, src_addr);

  // Start processing again.
  mode_ = NORMAL;
  ProcessBufferedTxns();
}

void SegmentedServer::HandleStartAck(const StartAck& start_ack,
                                     const UdpAddress& src_addr) {
  VLOG(1) << "Received StartAck from " << src_addr << " with epoch "
          << start_ack.epoch() << ".";

  // We cannot receive acks for epochs in the future!
  CHECK_LE(start_ack.epoch(), epoch_);

  if (start_ack.epoch() < epoch_) {
    VLOG(1) << "SegmentedServer received a StartAck for epoch "
            << start_ack.epoch() << " which is earlier than the current epoch "
            << epoch_ << ", so the SegmentedServer is ignoring this StartAck.";
    return;
  }

  CHECK_EQ(start_ack.epoch(), epoch_);
  if (mode_ == NORMAL) {
    VLOG(1) << "SegmentedServer received a StartAck with epoch "
            << start_ack.epoch() << " but is in normal mode in epoch " << epoch_
            << " so it ignoring the message.";
    return;
  }

  CHECK_EQ(mode_, WAITING_FOR_START_ACKS);
  start_acks_.insert(start_ack.replica_index());
  if (start_acks_.size() < cluster_.Size() - 1) {
    // We haven't yet received acks from the other replicas.
    return;
  }

  VLOG(1) << "SegmentedServer received StartAcks from all other replicas, so "
             "is transitioning into normal mode.";
  CHECK_EQ(start_acks_.size(), cluster_.Size() - 1);
  mode_ = NORMAL;
  start_acks_.clear();
  resend_start_timer_.Stop();
  ProcessBufferedTxns();
}

// TODO(mwhittaker): Right now, transactions are not annotated with client ids,
// so it's possible to execute the same transaction multiple times. However,
// invariant-confluence doesn't guarantee that transactions aren't executed
// twice, so it doesn't actually violate any guarantees. Still, it would easy
// to avoid redundantly executing the same transaction multiple times.
void SegmentedServer::ProcessBufferedTxns() {
  CHECK_EQ(mode_, NORMAL);

  auto it = pending_txn_requests_.begin();
  while (it != pending_txn_requests_.end()) {
    std::string reply;
    SyncStatus status = object_->ExecTxnSegmented(it->txn.txn(), &reply);
    if (status == SyncStatus::EXECUTED_LOCALLY) {
      // Reply to the client.
      ServerMessage msg;
      msg.mutable_txn_reply()->set_request_id(it->txn.request_id());
      msg.mutable_txn_reply()->set_reply(reply);
      SendTo(msg, it->src_addr);

      // Send merge requests if necessary.
      num_requests_serviced_++;
      if (num_requests_serviced_ % num_requests_per_gossip_ == 0) {
        SendMergeRequest();
      }

      it = pending_txn_requests_.erase(it);
    } else {
      CHECK_EQ(status, SyncStatus::REQUIRES_SYNC);
      // Transition to sync mode and save the transaction for later execution.
      // TODO(mwhittaker): Avoid redundant copies of pending_sync_txn_.
      mode_ = SYNCING_LEADER;
      CHECK(!pending_sync_txn_);
      pending_sync_txn_ = std::unique_ptr<PendingTxn>(new PendingTxn(*it));
      pending_txn_requests_.erase(it);

      // Increment the epoch and send SyncRequests to other replicas.
      epoch_++;
      VLOG(1) << "Transaction requires global sync. Sending SyncRequest "
                 "messages to other replicas with epoch "
              << epoch_ << ".";
      ServerMessage msg;
      msg.mutable_sync_request()->set_replica_index(replica_index_);
      msg.mutable_sync_request()->set_epoch(epoch_);
      const std::string msg_str = ProtoToString(msg);
      for (std::size_t i = 0; i < cluster_.Size(); ++i) {
        if (i != replica_index_) {
          SendTo(msg_str, cluster_.UdpAddrs()[i]);
        }
      }
      resend_sync_request_timer_.Start();

      return;
    }
  }
}

void SegmentedServer::SendMergeRequest() {
  // We could be sending this merge request to ourselves. While this is
  // inefficient, it's not incorrect.
  int dst_replica = RandomInt(0, cluster_.Size());
  const UdpAddress& dst_addr = cluster_.UdpAddrs()[dst_replica];

  ServerMessage msg;
  msg.mutable_merge_request()->set_object(object_->Get());
  msg.mutable_merge_request()->set_epoch(epoch_);
  SendTo(msg, dst_addr);
}

void SegmentedServer::ResendSyncRequest() {
  CHECK_EQ(mode_, SYNCING_LEADER);
  VLOG(1) << "SegmentedServer sync leader resending sync request to all other "
             "replicas.";

  ServerMessage msg;
  msg.mutable_sync_request()->set_replica_index(replica_index_);
  msg.mutable_sync_request()->set_epoch(epoch_);
  const std::string msg_str = ProtoToString(msg);
  for (std::size_t i = 0; i < cluster_.Size(); ++i) {
    if (i != replica_index_ && pending_sync_replies_.count(i) == 0) {
      SendTo(msg_str, cluster_.UdpAddrs()[i]);
    }
  }

  resend_sync_request_timer_.Reset();
}

void SegmentedServer::ResendStart() {
  CHECK_EQ(mode_, WAITING_FOR_START_ACKS);
  VLOG(1)
      << "SegmentedServer sync leader resending start to all other replicas.";

  // Send Start messages to the other replicas that haven't acked.
  const std::string start_s = ProtoToString(pending_start_);
  for (replica_index_t i = 0; i < cluster_.Size(); ++i) {
    if (i != replica_index_ && start_acks_.count(i) == 0) {
      SendTo(start_s, cluster_.UdpAddrs()[i]);
    }
  }

  resend_start_timer_.Reset();
}
