#ifndef TWO_INTS_H_
#define TWO_INTS_H_

#include <cstdint>

#include "object.h"
#include "two_ints.pb.h"

#if 0
class TwoInts : public Object {
 public:
  TwoInts(std::size_t segment_length) : segment_length_(segment_length) {}

  std::string Run(const std::string& txn) override;
  SyncStatus RunSegmented(const std::string& txn, std::string* reply) override;
  void Merge(const std::string& o) override;
  void Set(const std::string& o) override;
  std::string Get() override;

 private:
  std::size_t segment_length_;
  std::int64_t x_ = 0;
  std::int64_t y_ = 0;
};
#endif

#endif  //  TWO_INTS_H_
