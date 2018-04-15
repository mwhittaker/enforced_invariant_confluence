#include "client.h"

#include <chrono>

#include "glog/logging.h"

#include "proto_util.h"
#include "rand_util.h"
#include "server.pb.h"

Client::Client(ServerType server_type, const Cluster& server_cluster,
               Loop* loop)
    : Loop::Actor(loop),
      server_type_(server_type),
      server_cluster_(server_cluster) {
  resend_pending_txn_timer_ = loop->RegisterTimer(
      std::chrono::milliseconds(400), [this]() { ResendPendingTxn(); });
}

UdpAddress Client::GetServerAddress() const {
  // Paxos clients always have to communicate with the 0th server.
  if (server_type_ == PAXOS) {
    return server_cluster_.UdpAddrs()[0];
  }

  // Otherwise, we return a random address.
  const int index = RandomInt(0, server_cluster_.Size());
  return server_cluster_.UdpAddrs()[index];
}

void Client::SendTxnRequest(const std::string& txn_request,
                            const UdpAddress& dst_addr) {
  CHECK(!pending_);
  VLOG(1) << "Sending transaction to " << dst_addr << ".";

  // Save pending transaction.
  pending_ = true;
  ++request_id_;
  pending_txn_request_ = txn_request;
  pending_dst_addr_ = dst_addr;

  // Send transaction.
  ServerMessage request;
  request.mutable_txn_request()->set_txn(txn_request);
  request.mutable_txn_request()->set_request_id(request_id_);
  SendTo(request, dst_addr);

  // Start the timer.
  resend_pending_txn_timer_.Start();
}

void Client::OnRecv(const std::string& msg, const UdpAddress& src_addr) {
  VLOG(1) << "Received reply from " << src_addr << ".";

  // If we're not waiting for a response, then we ignore this message.
  if (!pending_) {
    return;
  }

  const auto reply = ProtoFromString<ServerMessage>(msg);
  CHECK(reply.has_txn_reply());

  // If we receive an old response, we ignore it.
  if (reply.txn_reply().request_id() != request_id_) {
    return;
  }

  // We're no longer pending!
  pending_ = false;
  resend_pending_txn_timer_.Stop();
  OnTxnRply(reply.txn_reply().reply(), src_addr);
}

void Client::Close() {
  Loop::Actor::Close();
  resend_pending_txn_timer_.Close();
}

void Client::ResendPendingTxn() {
  CHECK(pending_);

  // Send the request again.
  LOG(INFO) << "Resending pending transaction.";
  ServerMessage request;
  request.mutable_txn_request()->set_txn(pending_txn_request_);
  request.mutable_txn_request()->set_request_id(request_id_);
  SendTo(request, pending_dst_addr_);

  // Reset the timer.
  resend_pending_txn_timer_.Reset();
}
