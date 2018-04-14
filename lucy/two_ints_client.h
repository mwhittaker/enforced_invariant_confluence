#ifndef TWO_INTS_CLIENT_H_
#define TWO_INTS_CLIENT_H_

#include <cstdint>
#include <future>
#include <utility>

#include "client.h"

class TwoIntsClient : public Client {
 public:
  TwoIntsClient(ServerType server_type, const Cluster& server_cluster,
                Loop* loop)
      : Client(server_type, server_cluster, loop) {}

  enum Result { COMMITTED, ABORTED };

  void Get(std::promise<std::pair<std::int64_t, std::int64_t>>* promise);
  void IncrementX(std::promise<Result>* promise);
  void DecrementY(std::promise<Result>* promise);
  void Get(const UdpAddress& dst_addr,
           std::promise<std::pair<std::int64_t, std::int64_t>>* promise);
  void IncrementX(const UdpAddress& dst_addr, std::promise<Result>* promise);
  void DecrementY(const UdpAddress& dst_addr, std::promise<Result>* promise);

 protected:
  void OnTxnRply(const std::string& txn_reply,
                 const UdpAddress& src_addr) override;

 private:
  bool HasPendingPromise() const;

  std::promise<std::pair<std::int64_t, std::int64_t>>* get_promise_ = nullptr;
  std::promise<Result>* increment_x_promise_ = nullptr;
  std::promise<Result>* decrement_y_promise_ = nullptr;
};

#endif  //  TWO_INTS_CLIENT_H_
