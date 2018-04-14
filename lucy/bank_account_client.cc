#include "bank_account_client.h"

#include "glog/logging.h"

#include "bank_account.pb.h"
#include "proto_util.h"

void BankAccountClient::Get(std::promise<std::int64_t>* promise) {
  Get(GetServerAddress(), promise);
}

void BankAccountClient::Deposit(std::int64_t amount,
                                std::promise<Result>* promise) {
  Deposit(amount, GetServerAddress(), promise);
}

void BankAccountClient::Withdraw(std::int64_t amount,
                                 std::promise<Result>* promise) {
  Withdraw(amount, GetServerAddress(), promise);
}

void BankAccountClient::Get(const UdpAddress& dst_addr,
                            std::promise<std::int64_t>* promise) {
  CHECK(!HasPendingPromise());
  get_promise_ = promise;
  BankAccountTxnRequest request;
  request.mutable_get();
  SendTxnRequest(ProtoToString(request), dst_addr);
}

void BankAccountClient::Deposit(std::int64_t amount, const UdpAddress& dst_addr,
                                std::promise<Result>* promise) {
  CHECK(!HasPendingPromise());
  deposit_promise_ = promise;
  BankAccountTxnRequest request;
  request.mutable_deposit()->set_amount(amount);
  SendTxnRequest(ProtoToString(request), dst_addr);
}

void BankAccountClient::Withdraw(std::int64_t amount,
                                 const UdpAddress& dst_addr,
                                 std::promise<Result>* promise) {
  CHECK(!HasPendingPromise());
  withdraw_promise_ = promise;
  BankAccountTxnRequest request;
  request.mutable_withdraw()->set_amount(amount);
  SendTxnRequest(ProtoToString(request), dst_addr);
}

void BankAccountClient::OnTxnRply(const std::string& txn_reply,
                                  const UdpAddress& src_addr) {
  CHECK(HasPendingPromise());
  (void)src_addr;

  const auto reply = ProtoFromString<BankAccountTxnReply>(txn_reply);
  if (reply.has_get()) {
    CHECK(get_promise_ != nullptr);
    CHECK_EQ(reply.result(), BankAccountTxnReply::COMMITTED);
    get_promise_->set_value(reply.get().value());
    get_promise_ = nullptr;
  } else if (reply.has_deposit()) {
    CHECK(deposit_promise_ != nullptr);
    CHECK_EQ(reply.result(), BankAccountTxnReply::COMMITTED);
    deposit_promise_->set_value(COMMITTED);
    deposit_promise_ = nullptr;
  } else if (reply.has_withdraw()) {
    CHECK(withdraw_promise_ != nullptr);
    if (reply.result() == BankAccountTxnReply::COMMITTED) {
      withdraw_promise_->set_value(COMMITTED);
    } else {
      withdraw_promise_->set_value(ABORTED);
    }
    withdraw_promise_ = nullptr;
  } else {
    LOG(FATAL) << "Unrecognized transaction reply.";
  }
}

bool BankAccountClient::HasPendingPromise() const {
  return get_promise_ != nullptr || deposit_promise_ != nullptr ||
         withdraw_promise_ != nullptr;
}
