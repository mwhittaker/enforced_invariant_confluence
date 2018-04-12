#include "two_ints_client.h"

#include "glog/logging.h"

#include "two_ints.pb.h"

std::pair<std::int64_t, std::int64_t> TwoIntsClient::Get(
    const UdpAddress& dst_addr) {
  TwoIntsTxnRequest request;
  request.set_type(TwoIntsTxnRequest::GET);
  request.mutable_get();
  std::string request_str;
  request.SerializeToString(&request_str);

  TwoIntsTxnReply reply;
  reply.ParseFromString(ExecTxn(request_str, dst_addr));
  CHECK_EQ(reply.result(), TwoIntsTxnReply::COMMITTED);
  CHECK(reply.has_get());
  return {reply.get().x(), reply.get().y()};
}

TwoIntsClient::Result TwoIntsClient::IncrementX(const UdpAddress& dst_addr) {
  TwoIntsTxnRequest request;
  request.set_type(TwoIntsTxnRequest::INCREMENT_X);
  request.mutable_increment_x();
  std::string request_str;
  request.SerializeToString(&request_str);

  TwoIntsTxnReply reply;
  reply.ParseFromString(ExecTxn(request_str, dst_addr));
  if (reply.result() == TwoIntsTxnReply::COMMITTED) {
    CHECK(reply.has_increment_x());
    return COMMITTED;
  } else {
    return ABORTED;
  }
}

TwoIntsClient::Result TwoIntsClient::DecrementY(const UdpAddress& dst_addr) {
  TwoIntsTxnRequest request;
  request.set_type(TwoIntsTxnRequest::DECREMENT_Y);
  request.mutable_decrement_y();
  std::string request_str;
  request.SerializeToString(&request_str);

  TwoIntsTxnReply reply;
  reply.ParseFromString(ExecTxn(request_str, dst_addr));
  if (reply.result() == TwoIntsTxnReply::COMMITTED) {
    CHECK(reply.has_increment_x());
    return COMMITTED;
  } else {
    return ABORTED;
  }
}
