#include "host_port.h"

HostPort::HostPort(std::string host, std::uint16_t port)
    : host_(std::move(host)), port_(port) {}

HostPort::HostPort(const HostPortProto& proto)
    : host_(proto.host()), port_(proto.port()) {}

HostPortKey HostPort::Key() const { return HostPortKey(host_, port_); }
