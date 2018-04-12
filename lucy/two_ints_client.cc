#include "two_ints_client.h"

#include "glog/logging.h"

#include "proto_util.h"
#include "two_ints.pb.h"

std::pair<std::int64_t, std::int64_t> TwoIntsClient::Get() {
  return Get(GetServerAddress());
}

TwoIntsClient::Result TwoIntsClient::IncrementX() {
  return IncrementX(GetServerAddress());
}

TwoIntsClient::Result TwoIntsClient::DecrementY() {
  return DecrementY(GetServerAddress());
}

std::pair<std::int64_t, std::int64_t> TwoIntsClient::Get(
    const UdpAddress& dst_addr) {
  TwoIntsTxnRequest request;
  request.mutable_get();

  const std::string reply_str = ExecTxn(ProtoToString(request), dst_addr);
  const auto reply = ProtoFromString<TwoIntsTxnReply>(reply_str);
  CHECK_EQ(reply.result(), TwoIntsTxnReply::COMMITTED);
  CHECK(reply.has_get());
  return {reply.get().x(), reply.get().y()};
}

TwoIntsClient::Result TwoIntsClient::IncrementX(const UdpAddress& dst_addr) {
  TwoIntsTxnRequest request;
  request.mutable_increment_x();

  const std::string reply_str = ExecTxn(ProtoToString(request), dst_addr);
  const auto reply = ProtoFromString<TwoIntsTxnReply>(reply_str);
  if (reply.result() == TwoIntsTxnReply::COMMITTED) {
    CHECK(reply.has_increment_x());
    return COMMITTED;
  } else {
    return ABORTED;
  }
}

TwoIntsClient::Result TwoIntsClient::DecrementY(const UdpAddress& dst_addr) {
  TwoIntsTxnRequest request;
  request.mutable_decrement_y();

  const std::string reply_str = ExecTxn(ProtoToString(request), dst_addr);
  const auto reply = ProtoFromString<TwoIntsTxnReply>(reply_str);
  if (reply.result() == TwoIntsTxnReply::COMMITTED) {
    CHECK(reply.has_decrement_y());
    return COMMITTED;
  } else {
    return ABORTED;
  }
}
