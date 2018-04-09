#include "epoch.h"

Epoch::Epoch(std::uint64_t counter, replica_index_t replica_index) {
  epoch_proto_.set_counter(counter);
  epoch_proto_.set_replica_index(replica_index);
}

Epoch::Epoch(EpochProto epoch_proto) : epoch_proto_(std::move(epoch_proto)) {}

Epoch Epoch::Increment() const { return Epoch(Counter() + 1, ReplicaIndex()); }

EpochProto Epoch::ToProto() const { return epoch_proto_; }

Epoch Epoch::WithCounter(std::uint64_t counter) const {
  return Epoch(counter, ReplicaIndex());
}

std::uint64_t Epoch::Counter() const { return epoch_proto_.counter(); }

replica_index_t Epoch::ReplicaIndex() const {
  return epoch_proto_.replica_index();
}

EpochKey Epoch::Key() const { return EpochKey(Counter(), ReplicaIndex()); }
