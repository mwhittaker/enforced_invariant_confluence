#ifndef TRANSPORT_H_
#define TRANSPORT_H_

#include <chrono>
#include <functional>
#include <map>
#include <memory>
#include <mutex>
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
    Actor(const UdpAddress& addr, Loop* loop);
    Actor(Loop* loop);
    Actor(const Actor&) = delete;
    Actor(Actor&&) = delete;
    Actor& operator=(const Actor&) = delete;
    Actor& operator=(Actor&&) = delete;
    virtual ~Actor();

    void SendTo(const std::string& msg, const UdpAddress& addr);
    void SendTo(const google::protobuf::Message& proto, const UdpAddress& addr);
    virtual void Close();

   protected:
    virtual void OnRecv(const std::string& msg, const UdpAddress& src_addr) = 0;

   private:
    struct PendingSend {
      std::unique_ptr<uv_udp_send_t> send_request;
      std::uint64_t id;
      std::vector<char> data;
      Actor* actor;
    };

    void StartRecv();

    std::unique_ptr<uv_udp_t> socket_;
    std::uint64_t pending_send_id_ = 0;
    std::map<std::uint64_t, std::unique_ptr<PendingSend>> pending_sends_;
    bool closed_ = false;
  };

  class Timer {
   public:
    Timer() = default;
    Timer(std::unique_ptr<uv_timer_t> timer, callback_t callback,
          const std::chrono::milliseconds delay);
    Timer(Timer&&) = default;
    Timer(const Timer&) = delete;
    Timer& operator=(const Timer&) = delete;
    Timer& operator=(Timer&&) = default;
    ~Timer();

    void Start();
    void Stop();
    void Reset();
    void Close();

   private:
    std::unique_ptr<uv_timer_t> timer_;
    std::unique_ptr<callback_t> callback_;
    std::chrono::milliseconds delay_;
    bool closed_ = false;
  };

  Loop();
  Loop(const Loop&) = delete;
  Loop(Loop&&) = delete;
  Loop& operator=(const Loop&) = delete;
  Loop& operator=(Loop&&) = delete;
  ~Loop();

  Timer RegisterTimer(const std::chrono::milliseconds& delay,
                      const callback_t& callback);
  void RunFromAnotherThread(const callback_t& callback);
  void Run();
  void Stop();

 private:
  bool stopped_ = false;
  std::unique_ptr<uv_loop_t> loop_;
  std::unique_ptr<uv_async_t> async_;
  std::vector<callback_t> pending_callbacks_;
  std::mutex pending_callbacks_mutex_;
};

#endif  // TRANSPORT_H_
