#include <iostream>

#include "glog/logging.h"

#include "host_port.h"
#include "loop.h"

class EchoServer : public Loop::Actor {
 public:
  EchoServer(const HostPort& host_port, Loop* loop)
      : Loop::Actor(host_port, loop) {}

  void OnRecv(const std::string& msg, const UdpAddress& src_addr) override {
    std::cout << "[" << src_addr << "] " << msg << std::endl;
    if (msg != "ping") {
      SendTo(msg, src_addr);
    }
  }
};

int main(int, char* argv[]) {
  google::InitGoogleLogging(argv[0]);

  Loop loop;
  HostPort host_port("127.0.0.1", 9000);
  EchoServer server(host_port, &loop);

  std::cout << "EchoServer listening on " << host_port << std::endl;
  loop.Run();
}
