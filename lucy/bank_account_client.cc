#include "bank_account_client.h"

#include "glog/logging.h"

#include "bank_account.pb.h"

std::int64_t BankAccountClient::Get(const UdpAddress& dst_addr) {
  BankAccountTxnRequest request;
  request.set_type(BankAccountTxnRequest::GET);
  request.mutable_get();
  std::string request_str;
  request.SerializeToString(&request_str);

  BankAccountTxnReply reply;
  reply.ParseFromString(ExecTxn(request_str, dst_addr));
  CHECK(reply.has_get());
  CHECK_EQ(reply.result(), BankAccountTxnReply::COMMITTED);
  return reply.get().value();
}

BankAccountClient::Result BankAccountClient::Deposit(
    std::int64_t amount, const UdpAddress& dst_addr) {
  BankAccountTxnRequest request;
  request.set_type(BankAccountTxnRequest::DEPOSIT);
  request.mutable_deposit()->set_amount(amount);
  std::string request_str;
  request.SerializeToString(&request_str);

  BankAccountTxnReply reply;
  reply.ParseFromString(ExecTxn(request_str, dst_addr));
  CHECK(reply.has_deposit());
  CHECK_EQ(reply.result(), BankAccountTxnReply::COMMITTED);
  return COMMITTED;
}

BankAccountClient::Result BankAccountClient::Withdraw(
    std::int64_t amount, const UdpAddress& dst_addr) {
  BankAccountTxnRequest request;
  request.set_type(BankAccountTxnRequest::WITHDRAW);
  request.mutable_withdraw()->set_amount(amount);
  std::string request_str;
  request.SerializeToString(&request_str);

  BankAccountTxnReply reply;
  reply.ParseFromString(ExecTxn(request_str, dst_addr));
  CHECK(reply.has_withdraw());
  if (reply.result() == BankAccountTxnReply::COMMITTED) {
    return COMMITTED;
  } else {
    return ABORTED;
  }
}
