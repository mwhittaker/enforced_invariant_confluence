#include "client.h"

#include "glog/logging.h"

#include "server.pb.h"

std::string Client::Run(const std::string& txn, const UdpAddress& dst_addr) {
  // Send request.
  ServerMessage request;
  request.set_type(ServerMessage::TXN_REQUEST);
  request.mutable_txn_request()->set_txn(txn);
  std::string request_str;
  request.SerializeToString(&request_str);
  socket_.SendTo(request_str, dst_addr);

  // Get reply.
  std::string reply_str;
  socket_.RecvFrom(&reply_str, nullptr);
  ServerMessage reply;
  reply.ParseFromString(reply_str);
  CHECK_EQ(reply.type(), ServerMessage::TXN_REPLY);
  CHECK(reply.has_txn_reply());
  return reply.txn_reply().reply();
}
