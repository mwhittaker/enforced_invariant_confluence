#ifndef EPOCH_H_
#define EPOCH_H_

#include <cstdint>
#include <iostream>
#include <utility>

#include "comparable_by_key.h"
#include "server.h"
#include "server.pb.h"

using EpochKey = std::pair<std::uint64_t, replica_index_t>;
class Epoch : public ComparableByKey<Epoch, EpochKey> {
 public:
  Epoch(std::uint64_t counter, replica_index_t replica_index);
  Epoch(EpochProto epoch_proto);

  Epoch Increment() const;
  EpochProto ToProto() const;
  Epoch WithCounter(std::uint64_t counter) const;
  std::uint64_t Counter() const;
  replica_index_t ReplicaIndex() const;

  friend std::ostream& operator<<(std::ostream& out, const Epoch& epoch) {
    out << "(" << epoch.Counter() << ", " << epoch.ReplicaIndex() << ")";
    return out;
  }

 protected:
  EpochKey Key() const override;

 private:
  EpochProto epoch_proto_;
};

#endif  // EPOCH_H_
