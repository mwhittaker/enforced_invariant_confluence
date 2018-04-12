#include "bank_account.h"

#include "glog/logging.h"

#include "bank_account.pb.h"

BankAccount::BankAccount(std::size_t num_replicas, replica_index_t replica)
    : num_replicas_(num_replicas),
      replica_(replica),
      p_(/*count=*/num_replicas, /*value=*/0),
      n_(/*count=*/num_replicas, /*value=*/0) {
  CHECK_GT(num_replicas, 0);
  CHECK_GE(replica, 0);
  CHECK_LT(replica, num_replicas);
}

std::string BankAccount::Run(const std::string& txn) {
  BankAccountTxnRequest request;
  request.ParseFromString(txn);
  BankAccountTxnReply reply;

  switch (request.type()) {
    case BankAccountTxnRequest::DEPOSIT: {
      CHECK(request.has_deposit());
      p_[replica_] += request.deposit().amount();
      reply.set_result(BankAccountTxnReply::COMMITTED);
      reply.mutable_deposit();
      break;
    }
    case BankAccountTxnRequest::WITHDRAW: {
      CHECK(request.has_withdraw());
      if (Value() - request.withdraw().amount() >= 0) {
        n_[replica_] += request.withdraw().amount();
        reply.mutable_withdraw();
        reply.set_result(BankAccountTxnReply::COMMITTED);
      } else {
        reply.set_result(BankAccountTxnReply::ABORTED);
      }
      break;
    }
    case BankAccountTxnRequest::GET: {
      CHECK(request.has_get());
      reply.set_result(BankAccountTxnReply::COMMITTED);
      reply.mutable_get()->set_value(Value());
      break;
    }
    default:
      LOG(FATAL) << "Unrecognized transaction type.";
  }

  std::string s;
  reply.SerializeToString(&s);
  return s;
}

SyncStatus BankAccount::RunSegmented(const std::string& txn,
                                     std::string* reply) {
  BankAccountTxnRequest txn_request;
  txn_request.ParseFromString(txn);

  switch (txn_request.type()) {
    case BankAccountTxnRequest::DEPOSIT: {
      CHECK(txn_request.has_deposit());
      p_[replica_] += txn_request.deposit().amount();
      BankAccountTxnReply txn_reply;
      txn_reply.set_result(BankAccountTxnReply::COMMITTED);
      txn_reply.mutable_deposit();
      txn_reply.SerializeToString(reply);
      return SyncStatus::EXECUTED_LOCALLY;
    }
    case BankAccountTxnRequest::WITHDRAW: {
      CHECK(txn_request.has_withdraw());
      return SyncStatus::REQUIRES_SYNC;
    }
    case BankAccountTxnRequest::GET: {
      CHECK(txn_request.has_get());
      BankAccountTxnReply txn_reply;
      txn_reply.set_result(BankAccountTxnReply::COMMITTED);
      txn_reply.mutable_get()->set_value(Value());
      txn_reply.SerializeToString(reply);
      return SyncStatus::EXECUTED_LOCALLY;
    }
    default:
      LOG(FATAL) << "Unrecognized transaction type.";
  }
}

void BankAccount::Merge(const std::string& o) {
  BankAccountProto proto;
  proto.ParseFromString(o);
  CHECK_EQ(num_replicas_, proto.p_size()) << proto.p_size();
  CHECK_EQ(num_replicas_, proto.n_size()) << proto.n_size();
  for (std::size_t i = 0; i < num_replicas_; ++i) {
    p_[i] = std::max(p_[i], proto.p(i));
    n_[i] = std::max(n_[i], proto.n(i));
  }
}

void BankAccount::Set(const std::string& o) {
  BankAccountProto proto;
  proto.ParseFromString(o);
  CHECK_EQ(num_replicas_, proto.p_size()) << proto.p_size();
  CHECK_EQ(num_replicas_, proto.n_size()) << proto.n_size();
  for (std::size_t i = 0; i < num_replicas_; ++i) {
    p_[i] = proto.p(i);
    n_[i] = proto.n(i);
  }
}

std::string BankAccount::Get() {
  BankAccountProto proto;
  for (std::int64_t pi : p_) {
    proto.add_p(pi);
  }
  for (std::int64_t ni : n_) {
    proto.add_n(ni);
  }
  std::string s;
  proto.SerializeToString(&s);
  return s;
}

std::int64_t BankAccount::Value() const {
  std::int64_t value = 0;
  for (std::int64_t x : p_) {
    value += x;
  }
  for (std::int64_t x : n_) {
    value -= x;
  }
  return value;
}
