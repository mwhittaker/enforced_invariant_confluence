#include "bank_account_client.h"

#include "glog/logging.h"

#include "bank_account.pb.h"

std::int64_t BankAccountClient::Get(const UdpAddress& dst_addr) {
  BankAccountTxnRequest request;
  request.set_type(BankAccountTxnRequest::GET);
  std::string request_str;
  request.SerializeToString(&request_str);

  BankAccountTxnReply reply;
  reply.ParseFromString(Run(request_str, dst_addr));
  CHECK(reply.has_get_reply());
  return reply.get_reply().value();
}

BankAccountClient::Result BankAccountClient::Deposit(
    std::int64_t amount, const UdpAddress& dst_addr) {
  BankAccountTxnRequest request;
  request.set_type(BankAccountTxnRequest::DEPOSIT);
  request.mutable_deposit_request()->set_amount(amount);
  std::string request_str;
  request.SerializeToString(&request_str);

  BankAccountTxnReply reply;
  reply.ParseFromString(Run(request_str, dst_addr));
  CHECK(reply.has_deposit_reply());
  if (reply.deposit_reply().result() == BankAccountDepositReply::COMMITTED) {
    return COMMITTED;
  } else {
    return ABORTED;
  }
}

BankAccountClient::Result BankAccountClient::Withdraw(
    std::int64_t amount, const UdpAddress& dst_addr) {
  BankAccountTxnRequest request;
  request.set_type(BankAccountTxnRequest::WITHDRAW);
  request.mutable_withdraw_request()->set_amount(amount);
  std::string request_str;
  request.SerializeToString(&request_str);

  BankAccountTxnReply reply;
  reply.ParseFromString(Run(request_str, dst_addr));
  CHECK(reply.has_withdraw_reply());
  if (reply.withdraw_reply().result() == BankAccountWithdrawReply::COMMITTED) {
    return COMMITTED;
  } else {
    return ABORTED;
  }
}
