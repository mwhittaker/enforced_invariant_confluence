#ifndef TWO_INTS_H_
#define TWO_INTS_H_

#include <cstdint>

#include "object.h"
#include "two_ints.pb.h"

// A TwoInts object o is a pair (x, y) of integers merged by a a pairwise max:
//
//   (x1, y1) join (x2, y2) = (max x1 x2, max y1 y2)
//
// We have one transaction that increments x and one that decrements y. Our
// invariant is that x * y <= 0. We segment our state space into an infinite
// number of square segments of side length segment_length_. For example, if
// segment_length_ is 3, then our state space looks something like this:
//
//                  y
//                  |
//      # O O O # # # _ _ _ _ _ _
//      O # # # O O O _ _ _ _ _ _
//      O # # # O O O _ _ _ _ _ _
//      O # # # O O O _ _ _ _ _ _
//      # O O O # # # _ _ _ _ _ _
//      # O O O # # # _ _ _ _ _ _
//     -#-O-O-O-#-#-@-O-O-#-#-#-O- x
//      _ _ _ _ _ _ O O O # # # O
//      _ _ _ _ _ _ O O O # # # O
//      _ _ _ _ _ _ # # # O O O #
//      _ _ _ _ _ _ # # # O O O #
//      _ _ _ _ _ _ # # # O O O #
//      _ _ _ _ _ _ O O O # # # O
//                  |
//
// where (0, 0) is in two segments with the bottom-right segmented prioritized.
class TwoInts : public Object {
 public:
  TwoInts(std::size_t segment_length)
      : segment_length_(segment_length), segment_(PointToSegment(x_, y_)) {}

  std::string ExecTxn(const std::string& txn) override;
  SyncStatus ExecTxnSegmented(const std::string& txn,
                              std::string* reply) override;
  void Merge(const std::string& o) override;
  void Set(const std::string& o) override;
  std::string Get() override;

 private:
  struct Segment {
    std::int64_t top_left_x;
    std::int64_t top_left_y;
  };

  bool PointSatisfiesInvariant(std::int64_t x, std::int64_t y) const;
  bool PointSatisfiesSegmentInvariant(std::int64_t x, std::int64_t y,
                                      const Segment& segment) const;
  std::int64_t XToSegmentCorner(std::int64_t x) const;
  std::int64_t YToSegmentCorner(std::int64_t y) const;
  Segment PointToSegment(std::int64_t x, std::int64_t y) const;

  const std::size_t segment_length_;
  std::int64_t x_ = 0;
  std::int64_t y_ = 0;
  Segment segment_;
};

#endif  //  TWO_INTS_H_
