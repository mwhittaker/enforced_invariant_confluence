#ifndef BANK_ACCOUNT_H_
#define BANK_ACCOUNT_H_

#include <cstdint>
#include <vector>

#include "object.h"
#include "server.h"

class BankAccount : public Object {
 public:
  BankAccount(std::size_t num_replicas, replica_index_t replica);

  std::string ExecTxn(const std::string& txn) override;
  SyncStatus ExecTxnSegmented(const std::string& txn,
                              std::string* reply) override;
  void Merge(const std::string& o) override;
  void Set(const std::string& o) override;
  std::string Get() override;

 private:
  std::int64_t Value() const;

  std::size_t num_replicas_;
  replica_index_t replica_;
  std::vector<std::uint64_t> p_;
  std::vector<std::uint64_t> n_;
};

#endif  // BANK_ACCOUNT_H_
