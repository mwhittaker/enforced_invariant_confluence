#include "two_ints.h"

#include "glog/logging.h"

#include "proto_util.h"

std::string TwoInts::Run(const std::string& txn) {
  const auto request = ProtoFromString<TwoIntsTxnRequest>(txn);
  TwoIntsTxnReply reply;

  if (request.has_increment_x()) {
    if (PointSatisfiesInvariant(x_ + 1, y_)) {
      x_++;
      reply.set_result(TwoIntsTxnReply::COMMITTED);
      reply.mutable_increment_x();
    } else {
      reply.set_result(TwoIntsTxnReply::ABORTED);
    }
  } else if (request.has_decrement_y()) {
    if (PointSatisfiesInvariant(x_, y_ - 1)) {
      y_--;
      reply.set_result(TwoIntsTxnReply::COMMITTED);
      reply.mutable_decrement_y();
    } else {
      reply.set_result(TwoIntsTxnReply::ABORTED);
    }
  } else if (request.has_get()) {
    reply.set_result(TwoIntsTxnReply::COMMITTED);
    reply.mutable_get()->set_x(x_);
    reply.mutable_get()->set_y(y_);
  } else {
    LOG(FATAL) << "Unrecognized txn type.";
  }

  return ProtoToString(reply);
}

SyncStatus TwoInts::RunSegmented(const std::string& txn, std::string* reply) {
  const auto request = ProtoFromString<TwoIntsTxnRequest>(txn);

  if (request.has_increment_x()) {
    if (PointSatisfiesSegmentInvariant(x_ + 1, y_, segment_)) {
      x_++;

      TwoIntsTxnReply txn_reply;
      txn_reply.set_result(TwoIntsTxnReply::COMMITTED);
      txn_reply.mutable_increment_x();
      txn_reply.SerializeToString(reply);
      return SyncStatus::EXECUTED_LOCALLY;
    } else if (!PointSatisfiesInvariant(x_ + 1, y_)) {
      TwoIntsTxnReply txn_reply;
      txn_reply.set_result(TwoIntsTxnReply::ABORTED);
      txn_reply.SerializeToString(reply);
      return SyncStatus::EXECUTED_LOCALLY;
    } else {
      return SyncStatus::REQUIRES_SYNC;
    }
  } else if (request.has_decrement_y()) {
    if (PointSatisfiesSegmentInvariant(x_, y_ - 1, segment_)) {
      y_--;

      TwoIntsTxnReply txn_reply;
      txn_reply.set_result(TwoIntsTxnReply::COMMITTED);
      txn_reply.mutable_decrement_y();
      txn_reply.SerializeToString(reply);
      return SyncStatus::EXECUTED_LOCALLY;
    } else if (!PointSatisfiesInvariant(x_, y_ - 1)) {
      TwoIntsTxnReply txn_reply;
      txn_reply.set_result(TwoIntsTxnReply::ABORTED);
      txn_reply.SerializeToString(reply);
      return SyncStatus::EXECUTED_LOCALLY;
    } else {
      return SyncStatus::REQUIRES_SYNC;
    }
  } else if (request.has_get()) {
    TwoIntsTxnReply txn_reply;
    txn_reply.set_result(TwoIntsTxnReply::COMMITTED);
    txn_reply.mutable_get()->set_x(x_);
    txn_reply.mutable_get()->set_y(y_);
    txn_reply.SerializeToString(reply);
    return SyncStatus::EXECUTED_LOCALLY;
  } else {
    LOG(FATAL) << "Unrecognized txn type.";
  }
}

void TwoInts::Merge(const std::string& o) {
  TwoIntsProto proto;
  proto.ParseFromString(o);
  x_ = std::max(x_, proto.x());
  y_ = std::max(y_, proto.y());
  CHECK(PointSatisfiesInvariant(x_, y_)) << x_ << ", " << y_;
}

void TwoInts::Set(const std::string& o) {
  TwoIntsProto proto;
  proto.ParseFromString(o);
  x_ = proto.x();
  y_ = proto.y();
  segment_ = PointToSegment(x_, y_);
  CHECK(PointSatisfiesInvariant(x_, y_)) << x_ << ", " << y_;
}

std::string TwoInts::Get() {
  TwoIntsProto proto;
  proto.set_x(x_);
  proto.set_y(y_);
  std::string s;
  proto.SerializeToString(&s);
  return s;
}

bool TwoInts::PointSatisfiesInvariant(std::int64_t x, std::int64_t y) const {
  return x * y <= 0;
}

bool TwoInts::PointSatisfiesSegmentInvariant(std::int64_t x, std::int64_t y,
                                             const Segment& segment) const {
  std::int64_t length = static_cast<std::int64_t>(segment_length_);
  return (segment.top_left_x <= x && x < segment.top_left_x + length) &&
         (y <= segment.top_left_y && segment.top_left_y - length < y);
}

std::int64_t TwoInts::XToSegmentCorner(std::int64_t x) const {
  if (x >= 0) {
    return (x / segment_length_) * segment_length_;
  } else {
    return ((x / segment_length_) * segment_length_) - (segment_length_ - 1);
  }
}

std::int64_t TwoInts::YToSegmentCorner(std::int64_t y) const {
  if (y <= 0) {
    return (y / segment_length_) * segment_length_;
  } else {
    return ((y / segment_length_) * segment_length_) + (segment_length_ - 1);
  }
}

TwoInts::Segment TwoInts::PointToSegment(std::int64_t x, std::int64_t y) const {
  return Segment{XToSegmentCorner(x), YToSegmentCorner(y)};
}
