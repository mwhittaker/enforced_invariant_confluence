#ifndef TWO_INTS_H_
#define TWO_INTS_H_

#include <cstdint>

#include "object.h"

class TwoInts : public Object {
 public:
  void RunTransaction(const std::string& txn) override;
  void Merge(const std::string& o) override;

 private:
  std::int64_t x_ = 0;
  std::int64_t y_ = 0;
};

#endif  //  TWO_INTS_H_
