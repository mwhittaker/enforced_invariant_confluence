#include "two_ints_client.h"

#include "glog/logging.h"

#include "proto_util.h"
#include "two_ints.pb.h"

void TwoIntsClient::Get(
    std::promise<std::pair<std::int64_t, std::int64_t>>* promise) {
  return Get(GetServerAddress(), promise);
}

void TwoIntsClient::IncrementX(std::promise<Result>* promise) {
  return IncrementX(GetServerAddress(), promise);
}

void TwoIntsClient::DecrementY(std::promise<Result>* promise) {
  return DecrementY(GetServerAddress(), promise);
}

void TwoIntsClient::Get(
    const UdpAddress& dst_addr,
    std::promise<std::pair<std::int64_t, std::int64_t>>* promise) {
  CHECK(!HasPendingPromise());
  get_promise_ = promise;
  TwoIntsTxnRequest request;
  request.mutable_get();
  SendTxnRequest(ProtoToString(request), dst_addr);
}

void TwoIntsClient::IncrementX(const UdpAddress& dst_addr,
                               std::promise<Result>* promise) {
  CHECK(!HasPendingPromise());
  increment_x_promise_ = promise;
  TwoIntsTxnRequest request;
  request.mutable_increment_x();
  SendTxnRequest(ProtoToString(request), dst_addr);
}

void TwoIntsClient::DecrementY(const UdpAddress& dst_addr,
                               std::promise<Result>* promise) {
  CHECK(!HasPendingPromise());
  decrement_y_promise_ = promise;
  TwoIntsTxnRequest request;
  request.mutable_decrement_y();
  SendTxnRequest(ProtoToString(request), dst_addr);
}

void TwoIntsClient::OnTxnRply(const std::string& txn_reply,
                              const UdpAddress& src_addr) {
  CHECK(HasPendingPromise());
  (void)src_addr;

  const auto reply = ProtoFromString<TwoIntsTxnReply>(txn_reply);
  if (reply.has_get()) {
    CHECK(get_promise_ != nullptr);
    CHECK_EQ(reply.result(), TwoIntsTxnReply::COMMITTED);
    get_promise_->set_value({reply.get().x(), reply.get().y()});
    get_promise_ = nullptr;
  } else if (reply.has_increment_x()) {
    CHECK(increment_x_promise_ != nullptr);
    if (reply.result() == TwoIntsTxnReply::COMMITTED) {
      increment_x_promise_->set_value(COMMITTED);
    } else {
      increment_x_promise_->set_value(ABORTED);
    }
    increment_x_promise_ = nullptr;
  } else if (reply.has_decrement_y()) {
    CHECK(decrement_y_promise_ != nullptr);
    if (reply.result() == TwoIntsTxnReply::COMMITTED) {
      decrement_y_promise_->set_value(COMMITTED);
    } else {
      decrement_y_promise_->set_value(ABORTED);
    }
    decrement_y_promise_ = nullptr;
  } else {
    LOG(FATAL) << "Unrecognized transaction reply.";
  }
}

bool TwoIntsClient::HasPendingPromise() const {
  return get_promise_ != nullptr || increment_x_promise_ != nullptr ||
         decrement_y_promise_ != nullptr;
}
