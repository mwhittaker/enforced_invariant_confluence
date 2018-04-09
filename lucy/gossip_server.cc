#include "gossip_server.h"

#include "glog/logging.h"

#include "rand_util.h"

void GossipServer::Run() {
  LOG(INFO) << "GossipServer running on " << cluster_.UdpAddrs()[replica_index_]
            << ".";

  while (true) {
    std::string msg;
    UdpAddress src_addr;
    socket_.RecvFrom(&msg, &src_addr);

    ServerMessage proto;
    proto.ParseFromString(msg);
    switch (proto.type()) {
      case ServerMessage::MERGE_REQUEST: {
        CHECK(proto.has_merge_request());
        HandleMergeRequest(proto.merge_request(), src_addr);
        break;
      }
      case ServerMessage::TXN_REQUEST: {
        CHECK(proto.has_txn_request());
        HandleTxnRequest(proto.txn_request(), src_addr);
        break;
      }
      default: { LOG(FATAL) << "Unexpected server message type"; }
    }
  }
}

void GossipServer::HandleMergeRequest(const MergeRequest& merge_request,
                                      const UdpAddress& src_addr) {
  DLOG(INFO) << "Received MergeRequest from " << src_addr << ".";
  (void)src_addr;
  object_->Merge(merge_request.object());
}

void GossipServer::HandleTxnRequest(const TxnRequest& txn_request,
                                    const UdpAddress& src_addr) {
  DLOG(INFO) << "Received TxnRequest from " << src_addr << ".";
  ServerMessage msg;
  msg.set_type(ServerMessage::TXN_REPLY);
  msg.mutable_txn_reply()->set_reply(object_->Run(txn_request.txn()));
  std::string s;
  msg.SerializeToString(&s);
  socket_.SendTo(s, src_addr);

  num_requests_serviced_++;
  if (num_requests_serviced_ % num_requests_per_gossip_ == 0) {
    // We could be sending this merge request to ourselves. While this is
    // inefficient, it's not incorrect.
    int dst_replica = RandomInt(0, cluster_.Size());
    const UdpAddress& dst_addr = cluster_.UdpAddrs()[dst_replica];

    ServerMessage msg;
    msg.set_type(ServerMessage::MERGE_REQUEST);
    msg.mutable_merge_request()->set_object(object_->Get());
    std::string s;
    msg.SerializeToString(&s);
    socket_.SendTo(s, dst_addr);
  }
}
