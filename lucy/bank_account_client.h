#ifndef BANK_ACCOUNT_CLIENT_H_
#define BANK_ACCOUNT_CLIENT_H_

#include <cstdint>

#include "client.h"

class BankAccountClient : public Client {
 public:
  BankAccountClient(ServerType server_type, const Cluster& server_cluster)
      : Client(server_type, server_cluster) {}

  enum Result { COMMITTED, ABORTED };
  std::int64_t Get();
  Result Deposit(std::int64_t amount);
  Result Withdraw(std::int64_t amount);
  std::int64_t Get(const UdpAddress& dst_addr);
  Result Deposit(std::int64_t amount, const UdpAddress& dst_addr);
  Result Withdraw(std::int64_t amount, const UdpAddress& dst_addr);
};

#endif  //  BANK_ACCOUNT_CLIENT_H_
