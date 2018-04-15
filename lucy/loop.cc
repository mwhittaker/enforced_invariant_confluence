#include "loop.h"

#include "glog/logging.h"
#include "sys/socket.h"
#include "sys/types.h"

#include "proto_util.h"

// Actor ///////////////////////////////////////////////////////////////////////
Loop::Actor::Actor(const HostPort& host_port, Loop* loop)
    : socket_(new uv_udp_t{}) {
  // Init.
  int err = uv_udp_init(loop->loop_.get(), socket_.get());
  CHECK_EQ(err, 0) << uv_err_name(err) << ": " << uv_strerror(err);

  // Set up our address.
  struct sockaddr_in addr;
  err = uv_ip4_addr(host_port.Host().c_str(), host_port.Port(), &addr);
  CHECK_EQ(err, 0) << uv_err_name(err) << ": " << uv_strerror(err);
  const auto* sockaddr = reinterpret_cast<const struct sockaddr*>(&addr);

  // Bind.
  err = uv_udp_bind(socket_.get(), sockaddr, UV_UDP_REUSEADDR);
  CHECK_EQ(err, 0) << uv_err_name(err) << ": " << uv_strerror(err);

  // StartRecv.
  StartRecv();
}

Loop::Actor::Actor(const UdpAddress& addr, Loop* loop)
    : socket_(new uv_udp_t{}) {
  // Init.
  int err = uv_udp_init(loop->loop_.get(), socket_.get());
  CHECK_EQ(err, 0) << uv_err_name(err) << ": " << uv_strerror(err);

  // Bind.
  err = uv_udp_bind(socket_.get(), addr.SockAddr(), UV_UDP_REUSEADDR);
  CHECK_EQ(err, 0) << uv_err_name(err) << ": " << uv_strerror(err);

  // StartRecv.
  StartRecv();
}

Loop::Actor::Actor(Loop* loop) : socket_(new uv_udp_t{}) {
  // Init.
  int err = uv_udp_init(loop->loop_.get(), socket_.get());
  CHECK_EQ(err, 0) << uv_err_name(err) << ": " << uv_strerror(err);

  // StartRecv.
  StartRecv();
}

Loop::Actor::~Actor() {
  if (!closed_) {
    CHECK(socket_);
    Close();
  }
}

void Loop::Actor::StartRecv() {
  CHECK(!closed_);

  const auto alloc_callback =  //
      [](uv_handle_t* handle, std::size_t suggested_size, uv_buf_t* buf) {
        (void)handle;
        buf->base = new char[suggested_size];
        buf->len = suggested_size;
      };

  const auto recv_callback =  //
      [](uv_udp_t* handle, ssize_t nread, const uv_buf_t* buf,
         const struct sockaddr* sockaddr, unsigned flags) {

        // Take ownership of buf's data immediately since we want to guarantee
        // that it is freed.
        std::unique_ptr<char[]> data(buf->base);

        // Check that we received an entire UDP packet.
        CHECK(!(flags & UV_UDP_PARTIAL));

        // libuv invokes recv_callback like this after every message is
        // received.
        if (nread == 0 && sockaddr == nullptr) {
          return;
        }

        // Here's the documentation on nread from [1]. If addr is not null,
        // then nread shouldn't be zero. Moreover, if nread is negative, it is
        // an error.
        //
        // > Number of bytes that have been received. 0 if there is no more
        // > data to read. You may discard or repurpose the read buffer. Note
        // > that 0 may also mean that an empty datagram was received (in this
        // > case addr is not NULL). < 0 if a transmission error was detected.
        //
        // [1]: http://docs.libuv.org/en/v1.x/udp.html#c.uv_udp_recv_cb
        CHECK(sockaddr != nullptr);
        CHECK_GE(nread, 0) << uv_err_name(nread) << ": " << uv_strerror(nread);
        // TODO: We should really allow for both IPv4 and IPv6.
        CHECK_EQ(sockaddr->sa_family, AF_INET);

        Actor* actor = reinterpret_cast<Loop::Actor*>(handle->data);
        // TODO: We might be able to avoid copying this data.
        std::string msg(buf->base, nread);
        UdpAddress addr(*reinterpret_cast<const struct sockaddr_in*>(sockaddr));
        actor->OnRecv(msg, addr);
      };

  socket_->data = reinterpret_cast<void*>(this);
  uv_udp_recv_start(socket_.get(), alloc_callback, recv_callback);
}

void Loop::Actor::Close() {
  if (closed_) {
    VLOG(1) << "Actor already closed; not closing again.";
    return;
  }

  int err = uv_udp_recv_stop(socket_.get());
  CHECK_EQ(err, 0) << uv_err_name(err) << ": " << uv_strerror(err);

  // We cannot destruct socket_ until the close callback below is finished.
  // Thus, we have to put the pointer to the uv_udp_t in the uv_udp_t
  // itself and then delete it within the close callback.
  uv_udp_t* socket = socket_.release();
  socket->data = reinterpret_cast<void*>(socket);
  uv_close(reinterpret_cast<uv_handle_t*>(socket), [](uv_handle_t* handle) {
    VLOG(1) << "socket_ closed.";
    uv_udp_t* socket = reinterpret_cast<uv_udp_t*>(handle->data);
    delete socket;
  });

  closed_ = true;
}

void Loop::Actor::SendTo(const std::string& msg, const UdpAddress& addr) {
  CHECK(!closed_);

  // libuv manages memory in a somewhat annoying way. If we want to send a
  // string over UDP, we have to allocate the string on the heap, pack a
  // pointer to it in a uv_buf_t, and call uv_udp_send with the pointer. Then,
  // after the send callback is invoked, we have to free the memory. See [1]
  // for more details.
  //
  // To accomplish this, we allocate a PendingSend object on the heap and store
  // it in a map in the Actor. The PendingSend stores the send request and the
  // message data (in a vector). We shove a pointer to this PendingSend in the
  // send_request. When the send callback is called, we remove the PendingSend
  // from the Actor's map. The destructors will free both the send request and
  // the allocated memory stored in the vector.
  //
  // [1]: https://groups.google.com/forum/#!topic/libuv/MM4FsFjJGvs

  // Set up the PendingSend object.
  std::uint64_t pending_send_id = pending_send_id_++;
  std::unique_ptr<PendingSend> pending_send(new PendingSend{
      /*send_request=*/std::unique_ptr<uv_udp_send_t>(new uv_udp_send_t{}),  //
      /*id=*/pending_send_id,                                                //
      /*data=*/std::vector<char>(msg.begin(), msg.end()),                    //
      /*actor=*/this                                                         //
  });
  pending_send->send_request->data =
      reinterpret_cast<void*>(pending_send.get());

  // Send the message.
  uv_buf_t buf;
  buf.base = pending_send->data.data();
  buf.len = pending_send->data.size();
  const auto send_callback = [](uv_udp_send_t* send_request, int err) {
    CHECK_EQ(err, 0) << uv_err_name(err) << ": " << uv_strerror(err);
    auto* pending_send = reinterpret_cast<PendingSend*>(send_request->data);
    std::uint64_t id = pending_send->id;
    Actor* actor = pending_send->actor;
    actor->pending_sends_.erase(id);
  };
  int err = uv_udp_send(pending_send->send_request.get(), socket_.get(), &buf,
                        /*nbufs=*/1, addr.SockAddr(), send_callback);
  CHECK_EQ(err, 0) << uv_err_name(err) << ": " << uv_strerror(err);

  // Store the PendingSend for later.
  pending_sends_[pending_send_id] = std::move(pending_send);
}

void Loop::Actor::SendTo(const google::protobuf::Message& proto,
                         const UdpAddress& addr) {
  SendTo(ProtoToString(proto), addr);
}

// Timer ///////////////////////////////////////////////////////////////////////
Loop::Timer::Timer(std::unique_ptr<uv_timer_t> timer, callback_t callback,
                   const std::chrono::milliseconds delay)
    : timer_(std::move(timer)),
      callback_(new callback_t(callback)),
      delay_(delay) {
  // libuv doesn't allow us to pass state capturing lambdas as callbacks. If
  // we want to pass some state to the callback, we have to shove it in the
  // handle's data field.
  timer_->data = reinterpret_cast<void*>(callback_.get());
}

Loop::Timer::~Timer() {
  // If the timer was default initialized or if Close() was called, then timer_
  // is null.
  if (timer_) {
    CHECK(!closed_);
    Close();
  }
}

void Loop::Timer::Start() {
  CHECK(!closed_);
  auto callback = [](uv_timer_t* handle) {
    callback_t* f = reinterpret_cast<callback_t*>(handle->data);
    (*f)();
  };
  int err =
      uv_timer_start(timer_.get(), callback, delay_.count(), /*repeat=*/0);
  CHECK_EQ(err, 0) << uv_err_name(err) << ": " << uv_strerror(err);
}

void Loop::Timer::Reset() {
  CHECK(!closed_);
  Stop();
  Start();
}

void Loop::Timer::Stop() {
  CHECK(!closed_);
  int err = uv_timer_stop(timer_.get());
  CHECK_EQ(err, 0) << uv_err_name(err) << ": " << uv_strerror(err);
}

void Loop::Timer::Close() {
  if (closed_) {
    VLOG(1) << "Timer already closed; not closing again.";
    return;
  }

  Stop();

  // We cannot destruct timer_ until the close callback below is finished.
  // Thus, we have to put the pointer to the uv_timer_t in the uv_timer_t
  // itself and then delete it within the close callback.
  uv_timer_t* timer = timer_.release();
  timer->data = reinterpret_cast<void*>(timer);
  uv_close(reinterpret_cast<uv_handle_t*>(timer), [](uv_handle_t* handle) {
    VLOG(1) << "timer closed.";
    uv_timer_t* timer = reinterpret_cast<uv_timer_t*>(handle->data);
    delete timer;
  });

  closed_ = true;
}

// Loop ////////////////////////////////////////////////////////////////////////
Loop::Loop() : loop_(new uv_loop_t{}), async_(new uv_async_t{}) {
  VLOG(1) << "Initializing loop.";
  int err = uv_loop_init(loop_.get());
  CHECK_EQ(err, 0) << uv_err_name(err) << ": " << uv_strerror(err);

  VLOG(1) << "Initializing async.";
  async_->data = reinterpret_cast<void*>(this);
  const auto async_callback = [](uv_async_t* handle) {
    auto* loop = reinterpret_cast<Loop*>(handle->data);
    for (auto it = loop->pending_callbacks_.begin();
         it != loop->pending_callbacks_.end();
         it = loop->pending_callbacks_.erase(it)) {
      (*it)();
    }
  };
  err = uv_async_init(loop_.get(), async_.get(), async_callback);
  CHECK_EQ(err, 0) << uv_err_name(err) << ": " << uv_strerror(err);
}

Loop::~Loop() {
  Stop();
  int err = uv_loop_close(loop_.get());
  CHECK_EQ(err, 0) << uv_err_name(err) << ": " << uv_strerror(err);
}

Loop::Timer Loop::RegisterTimer(const std::chrono::milliseconds& delay,
                                const callback_t& callback) {
  CHECK(!stopped_);
  std::unique_ptr<uv_timer_t> timer(new uv_timer_t{});
  int err = uv_timer_init(loop_.get(), timer.get());
  CHECK_EQ(err, 0) << uv_err_name(err) << ": " << uv_strerror(err);
  return Loop::Timer(std::move(timer), callback, delay);
}

void Loop::RunFromAnotherThread(const callback_t& callback) {
  CHECK(!stopped_);
  pending_callbacks_.push_back(callback);
  uv_async_send(async_.get());
}

void Loop::Run() {
  CHECK(!stopped_);
  int err = uv_run(loop_.get(), UV_RUN_DEFAULT);
  VLOG(1) << "uv_run returned " << err;
}

void Loop::Stop() {
  CHECK(loop_);
  CHECK(async_);

  if (stopped_) {
    VLOG(1) << "Loop already stopped; not stopping again.";
    return;
  }

  // Close the async.
  uv_close(reinterpret_cast<uv_handle_t*>(async_.get()),
           [](uv_handle_t* handle) {
             VLOG(1) << "async_ closed.";
             (void)handle;
           });

  // See https://stackoverflow.com/a/25831688/3187068.
  VLOG(1) << "Stopping loop.";
  uv_stop(loop_.get());
  uv_walk(
      loop_.get(),
      [](uv_handle_t* handle, void*) {
        if (!uv_is_closing(handle)) {
          LOG(FATAL)
              << "Unclosing handle of type "
              << uv_handle_type_name(handle->type)
              << " found. You must close all handles before stopping the loop.";
        }
      },
      nullptr);

  int err = uv_run(loop_.get(), UV_RUN_DEFAULT);
  VLOG(1) << "uv_run returned " << err;
  err = uv_run(loop_.get(), UV_RUN_DEFAULT);
  VLOG(1) << "uv_run returned " << err;
  CHECK_EQ(err, 0) << uv_err_name(err) << ": " << uv_strerror(err);
  CHECK(!uv_loop_alive(loop_.get()));

  stopped_ = true;
}
