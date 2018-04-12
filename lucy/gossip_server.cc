#include "gossip_server.h"

#include "glog/logging.h"

#include "proto_util.h"
#include "rand_util.h"

void GossipServer::Run() {
  LOG(INFO) << "GossipServer running on " << cluster_.UdpAddrs()[replica_index_]
            << ".";

  while (true) {
    std::string msg;
    UdpAddress src_addr;
    socket_.RecvFrom(&msg, &src_addr);

    const auto proto = ProtoFromString<ServerMessage>(msg);
    if (proto.has_merge_request()) {
      HandleMergeRequest(proto.merge_request(), src_addr);
    } else if (proto.has_txn_request()) {
      HandleTxnRequest(proto.txn_request(), src_addr);
    } else if (proto.has_die()) {
      return;
    } else {
      LOG(FATAL) << "Unexpected server message type";
    }
  }
}

void GossipServer::HandleMergeRequest(const MergeRequest& merge_request,
                                      const UdpAddress& src_addr) {
  VLOG(1) << "Received MergeRequest from " << src_addr << ".";
  (void)src_addr;
  object_->Merge(merge_request.object());
}

void GossipServer::HandleTxnRequest(const TxnRequest& txn_request,
                                    const UdpAddress& src_addr) {
  VLOG(1) << "Received TxnRequest from " << src_addr << ".";
  ServerMessage msg;
  msg.mutable_txn_reply()->set_reply(object_->Run(txn_request.txn()));
  socket_.SendTo(ProtoToString(msg), src_addr);

  num_requests_serviced_++;
  if (num_requests_serviced_ % num_requests_per_gossip_ == 0) {
    // We could be sending this merge request to ourselves. While this is
    // inefficient, it's not incorrect.
    int dst_replica = RandomInt(0, cluster_.Size());
    const UdpAddress& dst_addr = cluster_.UdpAddrs()[dst_replica];

    ServerMessage msg;
    msg.mutable_merge_request()->set_object(object_->Get());
    socket_.SendTo(ProtoToString(msg), dst_addr);
  }
}
