#ifndef BANK_ACCOUNT_H_
#define BANK_ACCOUNT_H_

#include <cstdint>
#include <vector>

#include "object.h"

class BankAccount : public Object {
 public:
  BankAccount(int num_replicas, int replica);

  std::string Run(const std::string& txn) override;
  SyncStatus RunSegmented(const std::string& txn, std::string* reply) override;
  void Merge(const std::string& o) override;
  void Set(const std::string& o) override;
  std::string Get() override;

 private:
  std::int64_t Value() const;

  int num_replicas_;
  int replica_;
  std::vector<std::int64_t> p_;
  std::vector<std::int64_t> n_;
};

#endif  // BANK_ACCOUNT_H_
