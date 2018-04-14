#ifndef BANK_ACCOUNT_CLIENT_H_
#define BANK_ACCOUNT_CLIENT_H_

#include <cstdint>
#include <future>
#include <memory>

#include "client.h"

class BankAccountClient : public Client {
 public:
  BankAccountClient(ServerType server_type, const Cluster& server_cluster,
                    Loop* loop)
      : Client(server_type, server_cluster, loop) {}

  enum Result { COMMITTED, ABORTED };

  void Get(std::promise<std::int64_t>* promise);
  void Deposit(std::int64_t amount, std::promise<Result>* promise);
  void Withdraw(std::int64_t amount, std::promise<Result>* promise);

  void Get(const UdpAddress& dst_addr, std::promise<std::int64_t>* promise);
  void Deposit(std::int64_t amount, const UdpAddress& dst_addr,
               std::promise<Result>* promise);
  void Withdraw(std::int64_t amount, const UdpAddress& dst_addr,
                std::promise<Result>* promise);

 protected:
  void OnTxnRply(const std::string& txn_reply,
                 const UdpAddress& src_addr) override;

 private:
  bool HasPendingPromise() const;

  std::promise<std::int64_t>* get_promise_ = nullptr;
  std::promise<Result>* deposit_promise_ = nullptr;
  std::promise<Result>* withdraw_promise_ = nullptr;
};

#endif  //  BANK_ACCOUNT_CLIENT_H_
