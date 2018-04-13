#include <chrono>
#include <iostream>
#include <string>
#include <thread>

#include "glog/logging.h"

#include "host_port.h"
#include "loop.h"
#include "udp.h"

class EchoClient : public Loop::Actor {
 public:
  EchoClient(const HostPort& server_host_port, Loop* loop)
      : Loop::Actor(loop), server_addr_(server_host_port) {
    std::chrono::seconds duration(1);
    ping_timer_ = loop->RegisterTimer(duration, [this]() {
      Send("ping");
      ping_timer_.Reset();
    });
    ping_timer_.Start();
  }

  void OnRecv(const std::string& msg, const UdpAddress& src_addr) override {
    std::cout << "[" << src_addr << "] " << msg << std::endl;
  }

  void Send(const std::string& msg) { SendTo(msg, server_addr_); }

 private:
  UdpAddress server_addr_;
  Loop::Timer ping_timer_;
};

int main(int, char* argv[]) {
  google::InitGoogleLogging(argv[0]);

  Loop loop;
  HostPort host_port("127.0.0.1", 9000);
  EchoClient client(host_port, &loop);

  std::thread loop_thread([&] { loop.Run(); });

  std::string line;
  std::cout << "> " << std::flush;
  while (std::getline(std::cin, line)) {
    loop.RunFromAnotherThread([&client, line]() { client.Send(line); });
    std::cout << "> " << std::flush;
  }

  loop.Stop();
  loop_thread.join();
}
