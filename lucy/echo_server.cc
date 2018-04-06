#include <iostream>
#include <string>

#include "glog/logging.h"

#include "host_port.h"
#include "udp.h"

int main(int, char* argv[]) {
  google::InitGoogleLogging(argv[0]);

  UdpAddress server_addr(HostPort("localhost", 9000));
  UdpSocket socket = UdpSocket(server_addr);

  while (true) {
    // Receive.
    std::string msg;
    UdpAddress client_addr;
    socket.RecvFrom(&msg, &client_addr);
    std::cout << "[" << client_addr << "] " << msg << std::endl;

    // Send.
    socket.SendTo(msg, client_addr);
  }
}
