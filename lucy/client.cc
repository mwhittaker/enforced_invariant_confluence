#include "client.h"

#include "glog/logging.h"

#include "proto_util.h"
#include "rand_util.h"
#include "server.pb.h"

std::string Client::ExecTxn(const std::string& txn,
                            const UdpAddress& dst_addr) {
  VLOG(1) << "Sending transaction to " << dst_addr << ".";
  // Send request.
  ServerMessage request;
  request.mutable_txn_request()->set_txn(txn);
  socket_.SendTo(ProtoToString(request), dst_addr);

  // Get reply.
  std::string reply_str;
  socket_.RecvFrom(&reply_str, nullptr);
  VLOG(1) << "Received reply from " << dst_addr << ".";
  const auto reply = ProtoFromString<ServerMessage>(reply_str);
  CHECK(reply.has_txn_reply());
  return reply.txn_reply().reply();
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
