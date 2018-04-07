#ifndef OBJECT_H_
#define OBJECT_H_

#include <string>

enum class SyncStatus { EXECUTED_LOCALLY, REQUIRES_SYNC };

class Object {
 public:
  virtual std::string Run(const std::string& txn) = 0;
  virtual SyncStatus RunSegmented(const std::string& txn, std::string* reply);
  virtual void Merge(const std::string& o) = 0;
  virtual void Set(const std::string& o) = 0;
  virtual std::string Get() = 0;
};

#endif  // OBJECT_H_
