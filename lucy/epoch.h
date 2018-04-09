#ifndef EPOCH_H_
#define EPOCH_H_

#include <cstdint>
#include <iostream>
#include <utility>

#include "comparable_by_key.h"
#include "server.pb.h"

using EpochKey = std::pair<std::int64_t, std::int64_t>;
class Epoch : public ComparableByKey<Epoch, EpochKey> {
 public:
  Epoch(std::int64_t counter, std::int64_t replica_index);
  Epoch(EpochProto epoch_proto);

  Epoch Increment() const;
  EpochProto ToProto() const;
  std::int64_t Counter() const;
  std::int64_t ReplicaIndex() const;

  friend std::ostream& operator<<(std::ostream& out, const Epoch& epoch) {
    out << "(" << epoch.Counter() << " ," << epoch.ReplicaIndex() << ")";
    return out;
  }

 protected:
  EpochKey Key() const override;

 private:
  EpochProto epoch_proto_;
};

#endif  // EPOCH_H_
