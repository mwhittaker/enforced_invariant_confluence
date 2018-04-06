#ifndef HOST_PORT_H_
#define HOST_PORT_H_

#include <cstdint>
#include <iostream>
#include <string>
#include <utility>

#include "cluster.pb.h"
#include "comparable_by_key.h"

using HostPortKey = std::pair<const std::string&, const std::uint16_t>;
class HostPort : public ComparableByKey<HostPort, HostPortKey> {
 public:
  HostPort(std::string host, std::uint16_t port);
  HostPort(const HostPortProto& proto);

  friend std::ostream& operator<<(std::ostream& out,
                                  const HostPort& host_port) {
    out << host_port.host_ << ":" << host_port.port_;
    return out;
  }

 protected:
  HostPortKey Key() const override;

 private:
  const std::string host_;
  const std::uint16_t port_;
};

#endif  // HOST_PORT_H_
