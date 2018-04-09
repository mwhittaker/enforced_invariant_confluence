#include "segmented_server.h"

#include "glog/logging.h"

#include "object.h"
#include "rand_util.h"

void SegmentedServer::Run() {
  LOG(INFO) << "SegmentedServer listening on "
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
      case ServerMessage::MERGE_REQUEST: {
        CHECK(proto.has_merge_request());
        HandleMergeRequest(proto.merge_request(), src_addr);
        break;
      }
      case ServerMessage::SYNC_REQUEST: {
        CHECK(proto.has_sync_request());
        HandleSyncRequest(proto.sync_request(), src_addr);
        break;
      }
      case ServerMessage::SYNC_REPLY: {
        CHECK(proto.has_sync_reply());
        HandleSyncReply(proto.sync_reply(), src_addr);
        break;
      }
      case ServerMessage::START: {
        CHECK(proto.has_start());
        HandleStart(proto.start(), src_addr);
        break;
      }
      default: { LOG(FATAL) << "Unexpected server message type"; }
    }
  }
}

void SegmentedServer::HandleTxnRequest(const TxnRequest& txn_request,
                                       const UdpAddress& src_addr) {
  DLOG(INFO) << "Received TxnRequest from " << src_addr << ".";

  // Buffer the request in pending_txn_requests_. If we're in normal mode,
  // we'll execute it right away. If we're in sync mode, we'll process requests
  // in a FIFO order.
  pending_txn_requests_.push_back(PendingTxn{txn_request, src_addr});

  if (mode_ != NORMAL) {
    LOG(INFO) << "SegmentedServer received a transaction request during a "
                 "sync. The request is begin buffered for later execution.";
  } else {
    ProcessBufferedTxns();
  }
}

void SegmentedServer::HandleMergeRequest(const MergeRequest& merge_request,
                                         const UdpAddress& src_addr) {
  DLOG(INFO) << "Received MergeRequest from " << src_addr << ".";
  (void)src_addr;
  if (mode_ == NORMAL) {
    CHECK(merge_request.has_epoch());
    Epoch merge_epoch = Epoch(merge_request.epoch());

    CHECK(merge_epoch <= epoch_);
    if (merge_epoch == epoch_) {
      object_->Merge(merge_request.object());
    } else {
      LOG(INFO) << "SegmentedServer received a MergeRequest for epoch "
                << merge_epoch << " which is earlier than the current epoch "
                << epoch_
                << ". The SegmentedServer is ignoring this merge request";
    }
  } else {
    DLOG(INFO) << "SegmentedServer received a MergeRequest during a sync. The "
                  "MergeRequest is being ignored.";
  }
}

void SegmentedServer::HandleSyncRequest(const SyncRequest& sync_request,
                                        const UdpAddress& src_addr) {
  DLOG(INFO) << "Received SyncRequest from " << src_addr << ".";

  // Ignoring SyncRequests with older epochs accomplishes a couple of things:
  //
  //   (1) If this node is in normal mode, then this ignores old SyncRequests
  //       that were reordered or duplicated in the network.
  //   (2) If this node is in syncing follower or leader mode, then this
  //       ignores SyncRequests from a competing leader with a lower replica
  //       index.
  Epoch sync_epoch(sync_request.epoch());
  if (sync_epoch < epoch_) {
    LOG(INFO) << "SegmentedServer received a SyncRequest for epoch "
              << sync_epoch << " but it is in epoch " << epoch_
              << ", so it ignoring the request.";
    return;
  }

  // If the epoch is more up-to-date, then we transition to being a follower.
  // If we were previously a leader, though, we have to make sure to rebuffer
  // our pending sync transaction.
  if (mode_ == SYNCING_LEADER) {
    CHECK(pending_sync_txn_);
    pending_txn_requests_.push_front(*pending_sync_txn_);
    pending_sync_txn_.reset();
    pending_sync_replies_.erase(epoch_);
  }

  mode_ = SYNCING_FOLLOWER;
  epoch_ = sync_epoch;

  ServerMessage msg;
  msg.set_type(ServerMessage::SYNC_REPLY);
  msg.mutable_sync_reply()->set_replica_index(replica_index_);
  *msg.mutable_sync_reply()->mutable_epoch() = sync_epoch.ToProto();
  msg.mutable_sync_reply()->set_object(object_->Get());
  std::string s;
  msg.SerializeToString(&s);
  socket_.SendTo(s, src_addr);
}

void SegmentedServer::HandleSyncReply(const SyncReply& sync_reply,
                                      const UdpAddress& src_addr) {
  DLOG(INFO) << "Received SyncReply from " << src_addr << ".";

  // We cannot receive a sync reply for a sync request with an epoch higher
  // than our own because if we ever sent such a request, we would have updated
  // our epoch.
  Epoch sync_epoch(sync_reply.epoch());
  CHECK(sync_epoch <= epoch_);

  if (mode_ != SYNCING_LEADER) {
    LOG(INFO)
        << "SegmentedServer received a SyncReply for epoch " << sync_epoch
        << " but it is not a syncing leader, so it is ignoring the SyncReply.";
    return;
  }

  if (sync_epoch < epoch_) {
    LOG(INFO) << "SegmentedServer received a SyncReply for epoch " << sync_epoch
              << " but it is a syncing leader with epoch " << epoch_
              << ", so it is ignoring the SyncReply.";
    return;
  }

  CHECK(sync_epoch == epoch_ && mode_ == SYNCING_LEADER);
  pending_sync_replies_[epoch_].insert(
      {sync_reply.replica_index(), sync_reply});
  if (pending_sync_replies_[epoch_].size() < cluster_.Size() - 1) {
    // We haven't yet heard back from all the other replicas.
    return;
  }

  // Merge the objects from all the other replicas.
  for (const std::pair<const replica_index_t, SyncReply>& p :
       pending_sync_replies_[epoch_]) {
    const SyncReply& sync_reply = p.second;
    object_->Merge(sync_reply.object());
  }

  // Execute the pending sync transaction and reply to the client.
  CHECK(pending_sync_txn_);
  std::string reply = object_->Run(pending_sync_txn_->txn.txn());
  ServerMessage msg;
  msg.set_type(ServerMessage::TXN_REPLY);
  msg.mutable_txn_reply()->set_reply(reply);
  std::string reply_s;
  msg.SerializeToString(&reply_s);
  socket_.SendTo(reply_s, pending_sync_txn_->src_addr);

  // Send Start messages to the other replicas.
  ServerMessage start;
  start.set_type(ServerMessage::START);
  start.mutable_start()->set_object(object_->Get());
  *start.mutable_start()->mutable_epoch() = epoch_.ToProto();
  std::string start_s;
  msg.SerializeToString(&start_s);
  for (replica_index_t i = 0; i < cluster_.Size(); ++i) {
    if (i != replica_index_) {
      socket_.SendTo(start_s, cluster_.UdpAddrs()[i]);
    }
  }

  // Resume normal processing.
  pending_sync_replies_.erase(epoch_);
  pending_sync_txn_.reset();
  mode_ = NORMAL;
  ProcessBufferedTxns();
}

void SegmentedServer::HandleStart(const Start& start,
                                  const UdpAddress& src_addr) {
  DLOG(INFO) << "Received Start from " << src_addr << ".";

  // This start has to be a lingering start from the past. If it were from the
  // present or the future, the replica that sent it would have to have
  // received a StartReply from us which means that we would have updated our
  // epoch to be at least as big as it, if not bigger.
  Epoch start_epoch(start.epoch());
  CHECK(start_epoch <= epoch_) << start_epoch;

  if (mode_ == NORMAL) {
    LOG(INFO) << "SegmentedServer received a Start with epoch " << start_epoch
              << " but is in normal mode in epoch " << epoch_
              << " so it ignoring the message.";
    return;
  }

  // If the start_epoch is from the past, then we just ignore it. It is a
  // duplicated or re-ordered message.
  if (start_epoch < epoch_) {
    LOG(INFO) << "SegmentedServer received a start epoch " << start_epoch
              << " but is syncing with current epoch " << epoch_
              << ". The SegmentedServer is ignoring the Start.";
    return;
  }

  // If the start epoch is the same as the current epoch, then we must be a
  // syncing follower. In order for the syncing leader to have sent the start,
  // it would have had to receive a SyncReply from us. When we sent the
  // SyncReply, we would have transitionined into SYNCING_FOLLOWER mode.
  CHECK(start_epoch == epoch_);
  CHECK(mode_ == SYNCING_FOLLOWER);
  mode_ = NORMAL;
  ProcessBufferedTxns();
}

// TODO(mwhittaker): Right now, transactions are not annotated with client ids,
// so it's possible to execute the same transaction multiple times. However,
// invariant-confluence doesn't guarantee that transactions aren't executed
// twice, so it doesn't actually violate any guarantees. Still, it would easy
// to avoid redundantly executing the same transaction multiple times.
void SegmentedServer::ProcessBufferedTxns() {
  CHECK(mode_ == NORMAL);

  auto it = pending_txn_requests_.begin();
  while (it != pending_txn_requests_.end()) {
    std::string reply;
    SyncStatus status = object_->RunSegmented(it->txn.txn(), &reply);
    if (status == SyncStatus::EXECUTED_LOCALLY) {
      // Reply to the client.
      ServerMessage msg;
      msg.set_type(ServerMessage::TXN_REPLY);
      msg.mutable_txn_reply()->set_reply(reply);
      std::string s;
      msg.SerializeToString(&s);
      socket_.SendTo(s, it->src_addr);

      // Send merge requests if necessary.
      num_requests_serviced_++;
      if (num_requests_serviced_ % num_requests_per_gossip_ == 0) {
        SendMergeRequest();
      }

      it = pending_txn_requests_.erase(it);
    } else {
      CHECK(status == SyncStatus::REQUIRES_SYNC);

      // Transition to sync mode and save the transaction for later execution.
      // TODO(mwhittaker): Avoid redundant copies of pending_sync_txn_.
      mode_ = SYNCING_LEADER;
      CHECK(!pending_sync_txn_);
      pending_sync_txn_ = std::unique_ptr<PendingTxn>(new PendingTxn(*it));
      pending_txn_requests_.erase(it);

      // Increment the epoch and send SyncRequests to other replicas.
      epoch_ = epoch_.Increment();
      ServerMessage msg;
      msg.set_type(ServerMessage::SYNC_REQUEST);
      msg.mutable_sync_request()->set_replica_index(replica_index_);
      *msg.mutable_sync_request()->mutable_epoch() = epoch_.ToProto();
      std::string s;
      msg.SerializeToString(&s);
      for (std::size_t i = 0; i < cluster_.Size(); ++i) {
        if (i != replica_index_) {
          socket_.SendTo(s, cluster_.UdpAddrs()[i]);
        }
      }

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
  msg.set_type(ServerMessage::MERGE_REQUEST);
  msg.mutable_merge_request()->set_object(object_->Get());
  *msg.mutable_merge_request()->mutable_epoch() = epoch_.ToProto();
  std::string s;
  msg.SerializeToString(&s);
  socket_.SendTo(s, dst_addr);
}
