#ifndef PROTO_UTIL_H_
#define PROTO_UTIL_H_

#include <string>

#include "google/protobuf/message.h"

std::string ProtoToString(const google::protobuf::Message& proto);

template <typename T>
T ProtoFromString(const std::string& s) {
  T proto;
  proto.ParseFromString(s);
  return proto;
}

#endif  // PROTO_UTIL_H_
