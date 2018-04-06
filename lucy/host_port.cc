#include "host_port.h"

HostPort::HostPort(std::string host, std::uint16_t port)
    : host_(std::move(host)), port_(port) {}

HostPort::HostPort(const HostPortProto& proto)
    : host_(proto.host()), port_(proto.port()) {}

const std::string& HostPort::Host() const { return host_; }

std::uint16_t HostPort::Port() const { return port_; }

HostPortKey HostPort::Key() const { return HostPortKey(host_, port_); }
