#include "two_ints.h"

#include "two_ints.pb.h"

void TwoInts::RunTransaction(const std::string& s) {
  two_ints::Transaction txn;
  bool success = txn.ParseFromString(s);
  (void)success;
}

void TwoInts::Merge(const std::string& o) {
  (void)o;
  (void)x_;
  (void)y_;
}
