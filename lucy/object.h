#ifndef OBJECT_H_
#define OBJECT_H_

#include <string>

class Object {
 public:
  virtual void RunTransaction(const std::string& txn) = 0;
  virtual void Merge(const std::string& o) = 0;
};

#endif  // OBJECT_H_
