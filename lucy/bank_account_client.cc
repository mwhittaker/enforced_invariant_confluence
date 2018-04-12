#include "bank_account_client.h"

#include "glog/logging.h"

#include "bank_account.pb.h"
#include "proto_util.h"

std::int64_t BankAccountClient::Get() { return Get(GetServerAddress()); }

BankAccountClient::Result BankAccountClient::Deposit(std::int64_t amount) {
  return Deposit(amount, GetServerAddress());
}

BankAccountClient::Result BankAccountClient::Withdraw(std::int64_t amount) {
  return Withdraw(amount, GetServerAddress());
}

std::int64_t BankAccountClient::Get(const UdpAddress& dst_addr) {
  BankAccountTxnRequest request;
  request.mutable_get();

  const std::string reply_str = ExecTxn(ProtoToString(request), dst_addr);
  const auto reply = ProtoFromString<BankAccountTxnReply>(reply_str);
  CHECK(reply.has_get());
  CHECK_EQ(reply.result(), BankAccountTxnReply::COMMITTED);
  return reply.get().value();
}

BankAccountClient::Result BankAccountClient::Deposit(
    std::int64_t amount, const UdpAddress& dst_addr) {
  BankAccountTxnRequest request;
  request.mutable_deposit()->set_amount(amount);

  const std::string reply_str = ExecTxn(ProtoToString(request), dst_addr);
  const auto reply = ProtoFromString<BankAccountTxnReply>(reply_str);
  CHECK(reply.has_deposit());
  CHECK_EQ(reply.result(), BankAccountTxnReply::COMMITTED);
  return COMMITTED;
}

BankAccountClient::Result BankAccountClient::Withdraw(
    std::int64_t amount, const UdpAddress& dst_addr) {
  BankAccountTxnRequest request;
  request.mutable_withdraw()->set_amount(amount);

  const std::string reply_str = ExecTxn(ProtoToString(request), dst_addr);
  const auto reply = ProtoFromString<BankAccountTxnReply>(reply_str);
  if (reply.result() == BankAccountTxnReply::COMMITTED) {
    CHECK(reply.has_withdraw());
    return COMMITTED;
  } else {
    return ABORTED;
  }
}
