#ifndef TWO_INTS_CLIENT_H_
#define TWO_INTS_CLIENT_H_

#include <cstdint>
#include <utility>

#include "client.h"

class TwoIntsClient : public Client {
 public:
  enum Result { COMMITTED, ABORTED };

  std::pair<std::int64_t, std::int64_t> Get(const UdpAddress& dst_addr);
  Result IncrementX(const UdpAddress& dst_addr);
  Result DecrementY(const UdpAddress& dst_addr);
};

#endif  //  TWO_INTS_CLIENT_H_
