#ifndef TRANSPORT_H_
#define TRANSPORT_H_

#include <chrono>
#include <functional>
#include <map>
#include <memory>
#include <string>
#include <vector>

#include "google/protobuf/message.h"
#include "uv.h"

#include "udp.h"

class Loop {
 public:
  using callback_t = std::function<void(void)>;

  class Actor {
   public:
    Actor(const HostPort& host_port, Loop* loop);
    Actor(Loop* loop);
    void SendTo(const std::string& msg, const UdpAddress& addr);
    void SendTo(const google::protobuf::Message& proto, const UdpAddress& addr);
    void Stop();

    virtual void OnRecv(const std::string& msg, const UdpAddress& src_addr) = 0;

   private:
    struct PendingSend {
      std::unique_ptr<uv_udp_send_t> send_request;
      std::uint64_t id;
      std::vector<char> data;
      Actor* actor;
    };

    void Start();

    std::unique_ptr<uv_udp_t> socket_;
    std::uint64_t pending_send_id_ = 0;
    std::map<std::uint64_t, std::unique_ptr<PendingSend>> pending_sends_;
  };

  class Timer {
   public:
    Timer() = default;
    Timer(std::unique_ptr<uv_timer_t> timer, callback_t callback,
          const std::chrono::milliseconds delay);
    Timer(Timer&&) = default;
    Timer& operator=(Timer&&) = default;
    ~Timer();

    void Start();
    void Stop();
    void Reset();

   private:
    std::unique_ptr<uv_timer_t> timer_;
    std::unique_ptr<callback_t> callback_;
    std::chrono::milliseconds delay_;
  };

  Loop();
  ~Loop();

  Timer RegisterTimer(const std::chrono::milliseconds& delay,
                      const callback_t& callback);
  void RunFromAnotherThread(const callback_t& callback);
  void Run();
  void Stop();

 private:
  std::unique_ptr<uv_loop_t> loop_;
  std::unique_ptr<uv_async_t> async_;
  std::vector<callback_t> pending_callbacks_;
};

#endif  // TRANSPORT_H_