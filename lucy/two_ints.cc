#include "two_ints.h"

#include "glog/logging.h"

std::string TwoInts::Run(const std::string& txn) {
  TwoIntsTxnRequest txn_request;
  txn_request.ParseFromString(txn);

  TwoIntsTxnReply txn_reply;
  switch (txn_request.type()) {
    case TwoIntsTxnRequest::INCREMENT_X: {
      if (PointSatisfiesInvariant(x_ + 1, y_)) {
        x_++;
        txn_reply.set_result(TwoIntsTxnReply::COMMITTED);
        txn_reply.mutable_increment_x();
      } else {
        txn_reply.set_result(TwoIntsTxnReply::ABORTED);
      }
      break;
    }
    case TwoIntsTxnRequest::DECREMENT_Y: {
      if (PointSatisfiesInvariant(x_, y_ - 1)) {
        y_--;
        txn_reply.set_result(TwoIntsTxnReply::COMMITTED);
        txn_reply.mutable_decrement_y();
      } else {
        txn_reply.set_result(TwoIntsTxnReply::ABORTED);
      }
      break;
    }
    case TwoIntsTxnRequest::GET: {
      txn_reply.set_result(TwoIntsTxnReply::COMMITTED);
      txn_reply.mutable_get()->set_x(x_);
      txn_reply.mutable_get()->set_y(y_);
      break;
    }
    default: { LOG(FATAL) << "Unrecognized txn type."; }
  }

  std::string txn_reply_str;
  txn_reply.SerializeToString(&txn_reply_str);
  return txn_reply_str;
}

SyncStatus TwoInts::RunSegmented(const std::string& txn, std::string* reply) {
  TwoIntsTxnRequest txn_request;
  txn_request.ParseFromString(txn);
  switch (txn_request.type()) {
    case TwoIntsTxnRequest::INCREMENT_X: {
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
    }
    case TwoIntsTxnRequest::DECREMENT_Y: {
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
    }
    case TwoIntsTxnRequest::GET: {
      TwoIntsTxnReply txn_reply;
      txn_reply.set_result(TwoIntsTxnReply::COMMITTED);
      txn_reply.mutable_get()->set_x(x_);
      txn_reply.mutable_get()->set_y(y_);
      txn_reply.SerializeToString(reply);
      return SyncStatus::EXECUTED_LOCALLY;
    }
    default: { LOG(FATAL) << "Unrecognized txn type."; }
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
