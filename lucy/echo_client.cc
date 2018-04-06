#include <iostream>
#include <string>

#include "glog/logging.h"

#include "host_port.h"
#include "udp.h"

int main(int, char* argv[]) {
  google::InitGoogleLogging(argv[0]);

  UdpAddress server_addr(HostPort("localhost", 9000));
  UdpSocket socket = UdpSocket();

  std::string line;
  std::cout << "> " << std::flush;
  while (std::getline(std::cin, line)) {
    // Send.
    socket.SendTo(line, server_addr);

    // Receive.
    std::string msg;
    UdpAddress addr;
    socket.RecvFrom(&msg, &addr);
    std::cout << "[" << addr << "] " << msg << std::endl;

    // Prompt.
    std::cout << "> " << std::flush;
  }
}
