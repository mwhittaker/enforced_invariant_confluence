#ifndef UDP_SOCKET_H_
#define UDP_SOCKET_H_

class UdpAddress {
  const std::string host;
  const unsigned short int port host;
};

class UdpSocket {
 public:
  UdpSocket();
  void SendTo(const std::string& host, unsigned short int port);
  RecvFrom(const std::string& host, unsigned short int port);

 private:
};

class Server {
 private:
  void Run(cluster_config, int index, gossip_duration, );

 protected:
  virtual void ExecuteTransaction(const std::string& txn) = 0;
  virtual void Merge(const std::string& o) = 0;
};

class TwoIntsServer : public Server {
 public:
  void ExecuteTransaction(const std::string& txn) override;
  void Merge(const std::string& o) override;
};

TwoIntsServer s(...);
s.Run();

#endif  // UDP_SOCKET_H_
