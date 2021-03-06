#ifndef OBJECT_H_
#define OBJECT_H_

#include <iostream>
#include <string>

enum class SyncStatus { EXECUTED_LOCALLY, REQUIRES_SYNC };
std::ostream& operator<<(std::ostream& out, const SyncStatus status);

class Object {
 public:
  virtual ~Object() {}

  virtual std::string ExecTxn(const std::string& txn) = 0;
  virtual SyncStatus ExecTxnSegmented(const std::string& txn,
                                      std::string* reply);
  virtual void Merge(const std::string& o) = 0;
  virtual void Set(const std::string& o) = 0;
  virtual std::string Get() = 0;
};

#endif  // OBJECT_H_
