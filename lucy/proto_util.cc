#include "proto_util.h"

std::string ProtoToString(const google::protobuf::Message& proto) {
  std::string s;
  proto.SerializeToString(&s);
  return s;
}
