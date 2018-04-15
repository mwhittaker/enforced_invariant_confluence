#ifndef CLIENT_H_
#define CLIENT_H_

#include <string>

#include "benchmark.pb.h"
#include "cluster.h"
#include "loop.h"
#include "server.h"
#include "udp.h"

class Client : public Loop::Actor {
 public:
  void Close() override;

 protected:
  Client(ServerType server_type, const Cluster& server_cluster, Loop* loop);

  UdpAddress GetServerAddress() const;

  void SendTxnRequest(const std::string& txn_request,
                      const UdpAddress& dst_addr);
  virtual void OnTxnRply(const std::string& txn_reply,
                         const UdpAddress& src_addr) = 0;

 private:
  void OnRecv(const std::string& msg, const UdpAddress& src_addr) override;
  void ResendPendingTxn();

  const ServerType server_type_;
  const Cluster server_cluster_;

  // Pending transactions.
  std::uint64_t request_id_ = 0;
  bool pending_ = false;
  std::string pending_txn_request_;
  UdpAddress pending_dst_addr_;
  Loop::Timer resend_pending_txn_timer_;
};

#endif  // CLIENT_H_
