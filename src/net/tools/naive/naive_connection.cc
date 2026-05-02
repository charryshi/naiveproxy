// Copyright 2018 The Chromium Authors. All rights reserved.
// Copyright 2018 klzgrad <kizdiv@gmail.com>. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.
#ifdef UNSAFE_BUFFERS_BUILD
// TODO(crbug.com/40284755): Remove this and spanify to fix the errors.
#pragma allow_unsafe_buffers
#endif

#include "net/tools/naive/naive_connection.h"

#include <cstring>
#include <limits>
#include <string_view>
#include <utility>

#include "base/functional/bind.h"
#include "base/functional/callback_helpers.h"
#include "base/logging.h"
#include "base/rand_util.h"
#include "base/strings/strcat.h"
#include "base/task/single_thread_task_runner.h"
#include "base/time/time.h"
#include "build/build_config.h"
#include "net/base/io_buffer.h"
#include "net/base/load_flags.h"
#include "net/base/net_errors.h"
#include "net/base/privacy_mode.h"
#include "net/base/url_util.h"
#include "net/proxy_resolution/proxy_info.h"
#include "net/socket/client_socket_handle.h"
#include "net/socket/client_socket_pool_manager.h"
#include "net/socket/stream_socket.h"
#include "net/spdy/spdy_session.h"
#include "net/tools/naive/http_proxy_server_socket.h"
#include "net/tools/naive/naive_padding_socket.h"
#include "net/tools/naive/redirect_resolver.h"
#include "net/tools/naive/socks5_server_socket.h"
#include "url/scheme_host_port.h"

#if BUILDFLAG(IS_LINUX)
#include <linux/netfilter_ipv4.h>
#include <netinet/in.h>
#include <sys/socket.h>

#include "net/base/ip_endpoint.h"
#include "net/base/sockaddr_storage.h"
#include "net/socket/tcp_client_socket.h"
#endif
#include "net/socket/udp_server_socket.h"

namespace net {

namespace {
constexpr int kBufferSize = 64 * 1024;
constexpr size_t kSocksUdpHeaderMinSize = 4;
constexpr uint8_t kSocksAddressIPv4 = 0x01;
constexpr uint8_t kSocksAddressDomain = 0x03;
constexpr uint8_t kSocksAddressIPv6 = 0x04;
constexpr uint8_t kUotAddressIPv4 = 0x00;
constexpr uint8_t kUotAddressIPv6 = 0x01;
constexpr uint8_t kUotAddressDomain = 0x02;

void AppendUint16(std::string* out, uint16_t value) {
  out->push_back(static_cast<char>((value >> 8) & 0xff));
  out->push_back(static_cast<char>(value & 0xff));
}

bool ReadUint16(std::string_view in, size_t offset, uint16_t* value) {
  if (offset + 2 > in.size()) {
    return false;
  }
  *value = (static_cast<uint8_t>(in[offset]) << 8) |
           static_cast<uint8_t>(in[offset + 1]);
  return true;
}

bool EncodeSocksUdpToUotFrame(std::string_view packet, std::string* frame) {
  if (packet.size() < kSocksUdpHeaderMinSize || packet[0] != 0 ||
      packet[1] != 0 || packet[2] != 0) {
    return false;
  }
  size_t offset = 3;
  uint8_t atyp = static_cast<uint8_t>(packet[offset++]);
  frame->clear();
  if (atyp == kSocksAddressIPv4) {
    if (offset + 4 + 2 > packet.size()) {
      return false;
    }
    frame->push_back(static_cast<char>(kUotAddressIPv4));
    frame->append(packet.substr(offset, 4));
    offset += 4;
  } else if (atyp == kSocksAddressIPv6) {
    if (offset + 16 + 2 > packet.size()) {
      return false;
    }
    frame->push_back(static_cast<char>(kUotAddressIPv6));
    frame->append(packet.substr(offset, 16));
    offset += 16;
  } else if (atyp == kSocksAddressDomain) {
    if (offset >= packet.size()) {
      return false;
    }
    size_t domain_len = static_cast<uint8_t>(packet[offset]);
    if (offset + 1 + domain_len + 2 > packet.size()) {
      return false;
    }
    frame->push_back(static_cast<char>(kUotAddressDomain));
    frame->append(packet.substr(offset, 1 + domain_len));
    offset += 1 + domain_len;
  } else {
    return false;
  }
  frame->append(packet.substr(offset, 2));
  offset += 2;
  size_t payload_len = packet.size() - offset;
  if (payload_len > std::numeric_limits<uint16_t>::max()) {
    return false;
  }
  AppendUint16(frame, static_cast<uint16_t>(payload_len));
  frame->append(packet.substr(offset));
  return true;
}

bool EncodeUotFrameToSocksUdp(std::string_view address,
                              std::string_view payload,
                              std::string* packet) {
  if (address.empty()) {
    return false;
  }
  packet->clear();
  packet->append("\x00\x00\x00", 3);
  uint8_t atyp = static_cast<uint8_t>(address[0]);
  if (atyp == kUotAddressIPv4) {
    if (address.size() != 1 + 4 + 2) {
      return false;
    }
    packet->push_back(static_cast<char>(kSocksAddressIPv4));
    packet->append(address.substr(1));
  } else if (atyp == kUotAddressIPv6) {
    if (address.size() != 1 + 16 + 2) {
      return false;
    }
    packet->push_back(static_cast<char>(kSocksAddressIPv6));
    packet->append(address.substr(1));
  } else if (atyp == kUotAddressDomain) {
    if (address.size() < 2) {
      return false;
    }
    size_t domain_len = static_cast<uint8_t>(address[1]);
    if (address.size() != 1 + 1 + domain_len + 2) {
      return false;
    }
    packet->push_back(static_cast<char>(kSocksAddressDomain));
    packet->append(address.substr(1));
  } else {
    return false;
  }
  packet->append(payload);
  return true;
}

std::string EncodeUotAssociateRequest() {
  std::string request;
  request.push_back('\x00');  // IsConnect=false.
  request.push_back('\x01');  // SOCKS serializer IPv4 address family.
  request.append("\x00\x00\x00\x00", 4);
  request.append("\x00\x00", 2);
  return request;
}
}  // namespace

NaiveConnection::NaiveConnection(
    unsigned int id,
    ClientProtocol protocol,
    std::unique_ptr<PaddingType> negotiated_client_padding,
    const ProxyInfo& proxy_info,
    RedirectResolver* resolver,
    HttpNetworkSession* session,
    const NetworkAnonymizationKey& network_anonymization_key,
    const NetLogWithSource& net_log,
    std::unique_ptr<StreamSocket> accepted_socket,
    const NetworkTrafficAnnotationTag& traffic_annotation)
    : id_(id),
      protocol_(protocol),
      negotiated_client_padding_(std::move(negotiated_client_padding)),
      proxy_info_(proxy_info),
      resolver_(resolver),
      session_(session),
      network_anonymization_key_(network_anonymization_key),
      net_log_(net_log),
      next_state_(STATE_NONE),
      client_socket_(std::move(accepted_socket)),
      server_socket_handle_(std::make_unique<ClientSocketHandle>()),
      sockets_{nullptr, nullptr},
      errors_{OK, OK},
      write_pending_{false, false},
      early_pull_pending_(false),
      can_push_to_server_(false),
      early_pull_result_(ERR_IO_PENDING),
      full_duplex_(false),
      time_func_(&base::TimeTicks::Now),
      traffic_annotation_(traffic_annotation) {
  io_callback_ = base::BindRepeating(&NaiveConnection::OnIOComplete,
                                     weak_ptr_factory_.GetWeakPtr());
}

NaiveConnection::~NaiveConnection() {
  Disconnect();
}

int NaiveConnection::Connect(CompletionOnceCallback callback) {
  DCHECK(client_socket_);
  DCHECK_EQ(next_state_, STATE_NONE);
  DCHECK(!connect_callback_);

  if (full_duplex_) {
    return OK;
  }

  next_state_ = STATE_CONNECT_CLIENT;

  int rv = DoLoop(OK);
  if (rv == ERR_IO_PENDING) {
    connect_callback_ = std::move(callback);
  }
  return rv;
}

void NaiveConnection::Disconnect() {
  full_duplex_ = false;
  if (udp_socket_) {
    udp_socket_->Close();
    udp_socket_.reset();
  }
  // Closes server side first because latency is higher.
  if (server_socket_handle_->socket()) {
    server_socket_handle_->socket()->Disconnect();
  }
  client_socket_->Disconnect();

  next_state_ = STATE_NONE;
  connect_callback_.Reset();
  run_callback_.Reset();
}

void NaiveConnection::DoCallback(int result) {
  DCHECK_NE(result, ERR_IO_PENDING);
  DCHECK(connect_callback_);

  // Since Run() may result in Read being called,
  // clear connect_callback_ up front.
  std::move(connect_callback_).Run(result);
}

void NaiveConnection::OnIOComplete(int result) {
  DCHECK_NE(next_state_, STATE_NONE);
  int rv = DoLoop(result);
  if (rv != ERR_IO_PENDING) {
    DoCallback(rv);
  }
}

int NaiveConnection::DoLoop(int last_io_result) {
  DCHECK_NE(next_state_, STATE_NONE);
  int rv = last_io_result;
  do {
    State state = next_state_;
    next_state_ = STATE_NONE;
    switch (state) {
      case STATE_CONNECT_CLIENT:
        DCHECK_EQ(rv, OK);
        rv = DoConnectClient();
        break;
      case STATE_CONNECT_CLIENT_COMPLETE:
        rv = DoConnectClientComplete(rv);
        break;
      case STATE_CONNECT_SERVER:
        DCHECK_EQ(rv, OK);
        rv = DoConnectServer();
        break;
      case STATE_CONNECT_SERVER_COMPLETE:
        rv = DoConnectServerComplete(rv);
        break;
      default:
        rv = ERR_UNEXPECTED;
        break;
    }
  } while (rv != ERR_IO_PENDING && next_state_ != STATE_NONE);
  return rv;
}

int NaiveConnection::DoConnectClient() {
  next_state_ = STATE_CONNECT_CLIENT_COMPLETE;

  return client_socket_->Connect(io_callback_);
}

int NaiveConnection::DoConnectClientComplete(int result) {
  if (result < 0) {
    return result;
  }

  sockets_[kClient] = std::make_unique<NaivePaddingSocket>(
      client_socket_.get(), *negotiated_client_padding_, kClient);

  // For proxy client sockets, padding support detection is finished after the
  // first server response which means there will be one missed early pull. For
  // proxy server sockets (HttpProxyServerSocket), padding support detection is
  // done during client connect, so there shouldn't be any missed early pull.
  if (!GetServerPaddingType().has_value()) {
    early_pull_pending_ = false;
    early_pull_result_ = 0;
    next_state_ = STATE_CONNECT_SERVER;
    return OK;
  }

  early_pull_pending_ = true;
  Pull(kClient, kServer);
  if (early_pull_result_ != ERR_IO_PENDING) {
    // Pull has completed synchronously.
    if (early_pull_result_ <= 0) {
      return early_pull_result_ ? early_pull_result_ : ERR_CONNECTION_CLOSED;
    }
  }

  next_state_ = STATE_CONNECT_SERVER;
  return OK;
}

int NaiveConnection::DoConnectServer() {
  next_state_ = STATE_CONNECT_SERVER_COMPLETE;

  HostPortPair origin;
  if (protocol_ == ClientProtocol::kSocks5) {
    const auto* socket =
        static_cast<const Socks5ServerSocket*>(client_socket_.get());
    origin = socket->request_endpoint();
  } else if (protocol_ == ClientProtocol::kHttp) {
    const auto* socket =
        static_cast<const HttpProxyServerSocket*>(client_socket_.get());
    origin = socket->request_endpoint();
  } else if (protocol_ == ClientProtocol::kRedir) {
#if BUILDFLAG(IS_LINUX)
    const auto* socket =
        static_cast<const TCPClientSocket*>(client_socket_.get());
    IPEndPoint peer_endpoint;
    int rv;
    rv = socket->GetPeerAddress(&peer_endpoint);
    if (rv != OK) {
      LOG(ERROR) << "Connection " << id_
                 << " cannot get peer address: " << ErrorToShortString(rv);
      return rv;
    }
    int sd = socket->SocketDescriptorForTesting();
    SockaddrStorage dst;
    if (peer_endpoint.GetFamily() == ADDRESS_FAMILY_IPV4 ||
        peer_endpoint.address().IsIPv4MappedIPv6()) {
      rv = getsockopt(sd, SOL_IP, SO_ORIGINAL_DST, dst.addr(), &dst.addr_len);
    } else {
      rv = getsockopt(sd, SOL_IPV6, SO_ORIGINAL_DST, dst.addr(), &dst.addr_len);
    }
    if (rv == 0) {
      IPEndPoint ipe;
      if (ipe.FromSockAddr(dst.addr(), dst.addr_len)) {
        const auto& addr = ipe.address();
        auto name = resolver_->FindNameByAddress(addr);
        if (!name.empty()) {
          origin = HostPortPair(name, ipe.port());
        } else if (!resolver_->IsInResolvedRange(addr)) {
          origin = HostPortPair::FromIPEndPoint(ipe);
        } else {
          LOG(ERROR) << "Connection " << id_ << " to unresolved name for "
                     << addr.ToString();
          return ERR_ADDRESS_INVALID;
        }
      }
    } else {
      LOG(ERROR) << "Failed to get original destination address";
      return ERR_ADDRESS_INVALID;
    }
#else
    static_cast<void>(resolver_);
#endif
  }

  url::CanonHostInfo host_info;
  url::SchemeHostPort endpoint(
      "http", CanonicalizeHost(origin.HostForURL(), &host_info), origin.port(),
      url::SchemeHostPort::ALREADY_CANONICALIZED);
  if (!endpoint.IsValid()) {
    LOG(ERROR) << "Connection " << id_ << " to invalid origin "
               << origin.ToString();
    return ERR_ADDRESS_INVALID;
  }

  LOG(INFO) << "Connection " << id_ << " to " << origin.ToString() << " via "
            << proxy_info_.ToDebugString();

  // Ignores socket limit set by socket pool for this type of socket.
  return InitSocketHandleForHttpRequest(
      std::move(endpoint), LOAD_IGNORE_LIMITS, MAXIMUM_PRIORITY, session_,
      proxy_info_, {}, PRIVACY_MODE_DISABLED, network_anonymization_key_,
      SecureDnsPolicy::kDisable, SocketTag(), handles::kInvalidNetworkHandle,
      net_log_, server_socket_handle_.get(), io_callback_,
      ClientSocketPool::ProxyAuthCallback());
}

int NaiveConnection::DoConnectServerComplete(int result) {
  if (result < 0) {
    return result;
  }

  std::optional<PaddingType> server_padding_type = GetServerPaddingType();
  CHECK(server_padding_type.has_value());

  sockets_[kServer] = std::make_unique<NaivePaddingSocket>(
      server_socket_handle_->socket(), *server_padding_type, kServer);

  if (protocol_ == ClientProtocol::kSocks5) {
    auto* socket = static_cast<Socks5ServerSocket*>(client_socket_.get());
    if (socket->is_udp_associate()) {
      udp_socket_ = socket->TakeUdpSocket();
      if (!udp_socket_) {
        return ERR_SOCKS_CONNECTION_FAILED;
      }
      udp_mode_ = true;
    }
  }

  full_duplex_ = true;
  next_state_ = STATE_NONE;
  return OK;
}

int NaiveConnection::Run(CompletionOnceCallback callback) {
  DCHECK(sockets_[kServer]);
  DCHECK_EQ(next_state_, STATE_NONE);
  DCHECK(!connect_callback_);

  if (udp_mode_) {
    return RunUdpAssociate(std::move(callback));
  }

  // The client-side socket may be closed before the server-side
  // socket is connected.
  if (errors_[kClient] != OK || sockets_[kClient] == nullptr) {
    return errors_[kClient];
  }
  if (errors_[kServer] != OK) {
    return errors_[kServer];
  }

  run_callback_ = std::move(callback);

  bytes_passed_without_yielding_[kClient] = 0;
  bytes_passed_without_yielding_[kServer] = 0;

  yield_after_time_[kClient] =
      time_func_() + base::Milliseconds(kYieldAfterDurationMilliseconds);
  yield_after_time_[kServer] = yield_after_time_[kClient];

  can_push_to_server_ = true;
  // early_pull_result_ == 0 means the early pull was not started because
  // padding support was not yet known.
  if (!early_pull_pending_ && early_pull_result_ == 0) {
    Pull(kClient, kServer);
  } else if (!early_pull_pending_) {
    DCHECK_GT(early_pull_result_, 0);
    Push(kClient, kServer, early_pull_result_);
  }
  Pull(kServer, kClient);

  return ERR_IO_PENDING;
}

void NaiveConnection::Pull(Direction from, Direction to) {
  if (errors_[kClient] < 0 || errors_[kServer] < 0) {
    return;
  }

  int read_size = kBufferSize;
  read_buffers_[from] = base::MakeRefCounted<IOBufferWithSize>(kBufferSize);

  DCHECK(sockets_[from]);
  int rv = sockets_[from]->Read(
      read_buffers_[from].get(), read_size,
      base::BindOnce(&NaiveConnection::OnPullComplete,
                     weak_ptr_factory_.GetWeakPtr(), from, to));

  if (from == kClient && early_pull_pending_) {
    early_pull_result_ = rv;
  }

  if (rv != ERR_IO_PENDING) {
    OnPullComplete(from, to, rv);
  }
}

void NaiveConnection::Push(Direction from, Direction to, int size) {
  write_buffers_[to] = base::MakeRefCounted<DrainableIOBuffer>(
      std::move(read_buffers_[from]), size);
  write_pending_[to] = true;
  DCHECK(sockets_[to]);
  int rv = sockets_[to]->Write(
      write_buffers_[to].get(), write_buffers_[to]->BytesRemaining(),
      base::BindOnce(&NaiveConnection::OnPushComplete,
                     weak_ptr_factory_.GetWeakPtr(), from, to),
      traffic_annotation_);

  if (rv != ERR_IO_PENDING) {
    OnPushComplete(from, to, rv);
  }
}

void NaiveConnection::Disconnect(Direction side) {
  if (sockets_[side]) {
    sockets_[side]->Disconnect();
    sockets_[side] = nullptr;
    write_pending_[side] = false;
  }
}

bool NaiveConnection::IsConnected(Direction side) {
  return sockets_[side] != nullptr;
}

void NaiveConnection::OnBothDisconnected() {
  if (run_callback_) {
    int error = OK;
    if (errors_[kClient] != ERR_CONNECTION_CLOSED && errors_[kClient] < 0) {
      error = errors_[kClient];
    }
    if (errors_[kServer] != ERR_CONNECTION_CLOSED && errors_[kServer] < 0) {
      error = errors_[kServer];
    }
    std::move(run_callback_).Run(error);
  }
}

void NaiveConnection::OnPullError(Direction from, Direction to, int error) {
  DCHECK_LT(error, 0);

  errors_[from] = error;
  Disconnect(from);

  if (!write_pending_[to]) {
    Disconnect(to);
  }

  if (!IsConnected(from) && !IsConnected(to)) {
    OnBothDisconnected();
  }
}

void NaiveConnection::OnPushError(Direction from, Direction to, int error) {
  DCHECK_LE(error, 0);
  DCHECK(!write_pending_[to]);

  if (error < 0) {
    errors_[to] = error;
    Disconnect(kServer);
    Disconnect(kClient);
  } else if (!IsConnected(from)) {
    Disconnect(to);
  }

  if (!IsConnected(from) && !IsConnected(to)) {
    OnBothDisconnected();
  }
}

void NaiveConnection::OnPullComplete(Direction from, Direction to, int result) {
  if (from == kClient && early_pull_pending_) {
    early_pull_pending_ = false;
    early_pull_result_ = result ? result : ERR_CONNECTION_CLOSED;
  }

  if (result <= 0) {
    OnPullError(from, to, result ? result : ERR_CONNECTION_CLOSED);
    return;
  }

  if (from == kClient && !can_push_to_server_) {
    return;
  }

  Push(from, to, result);
}

void NaiveConnection::OnPushComplete(Direction from, Direction to, int result) {
  if (result >= 0 && write_buffers_[to] != nullptr) {
    bytes_passed_without_yielding_[from] += result;
    write_buffers_[to]->DidConsume(result);
    int size = write_buffers_[to]->BytesRemaining();
    if (size > 0) {
      int rv = sockets_[to]->Write(
          write_buffers_[to].get(), size,
          base::BindOnce(&NaiveConnection::OnPushComplete,
                         weak_ptr_factory_.GetWeakPtr(), from, to),
          traffic_annotation_);
      if (rv != ERR_IO_PENDING) {
        OnPushComplete(from, to, rv);
      }
      return;
    }
  }

  write_pending_[to] = false;
  // Checks for termination even if result is OK.
  OnPushError(from, to, result >= 0 ? OK : result);

  if (bytes_passed_without_yielding_[from] > kYieldAfterBytesRead ||
      time_func_() > yield_after_time_[from]) {
    bytes_passed_without_yielding_[from] = 0;
    yield_after_time_[from] =
        time_func_() + base::Milliseconds(kYieldAfterDurationMilliseconds);
    base::SingleThreadTaskRunner::GetCurrentDefault()->PostTask(
        FROM_HERE, base::BindOnce(&NaiveConnection::Pull,
                                  weak_ptr_factory_.GetWeakPtr(), from, to));
  } else {
    Pull(from, to);
  }
}

int NaiveConnection::RunUdpAssociate(CompletionOnceCallback callback) {
  DCHECK(udp_socket_);
  DCHECK(sockets_[kServer]);
  run_callback_ = std::move(callback);
  QueueServerWrite(EncodeUotAssociateRequest());
  StartUdpRecv();
  uot_read_state_ = 0;
  uot_next_read_size_ = 1;
  StartUotRead(uot_next_read_size_);
  return ERR_IO_PENDING;
}

void NaiveConnection::StartUdpRecv() {
  if (!udp_socket_ || errors_[kClient] < 0 || errors_[kServer] < 0) {
    return;
  }
  udp_read_buffer_ = base::MakeRefCounted<IOBufferWithSize>(kBufferSize);
  udp_recv_endpoint_ = std::make_unique<IPEndPoint>();
  int rv = udp_socket_->RecvFrom(
      udp_read_buffer_.get(), kBufferSize, udp_recv_endpoint_.get(),
      base::BindOnce(&NaiveConnection::OnUdpRecvComplete,
                     weak_ptr_factory_.GetWeakPtr()));
  if (rv != ERR_IO_PENDING) {
    OnUdpRecvComplete(rv);
  }
}

void NaiveConnection::OnUdpRecvComplete(int result) {
  if (result <= 0) {
    FinishRun(result < 0 ? result : ERR_CONNECTION_CLOSED);
    return;
  }
  if (!udp_client_endpoint_) {
    udp_client_endpoint_ = std::move(udp_recv_endpoint_);
  } else if (!(*udp_client_endpoint_ == *udp_recv_endpoint_)) {
    StartUdpRecv();
    return;
  }

  std::string frame;
  std::string_view packet(udp_read_buffer_->data(), result);
  if (EncodeSocksUdpToUotFrame(packet, &frame)) {
    QueueServerWrite(std::move(frame));
  }
  StartUdpRecv();
}

void NaiveConnection::OnUdpFrameWritten(int result) {
  udp_send_pending_ = false;
  udp_send_buffer_ = nullptr;
  if (result < 0) {
    FinishRun(result);
    return;
  }
  ProcessUotReadBuffer();
}

void NaiveConnection::StartUotRead(size_t size) {
  if (!sockets_[kServer] || errors_[kServer] < 0) {
    return;
  }
  read_buffers_[kServer] = base::MakeRefCounted<IOBufferWithSize>(size);
  int rv = sockets_[kServer]->Read(
      read_buffers_[kServer].get(), size,
      base::BindOnce(&NaiveConnection::OnUotReadComplete,
                     weak_ptr_factory_.GetWeakPtr()));
  if (rv != ERR_IO_PENDING) {
    OnUotReadComplete(rv);
  }
}

void NaiveConnection::OnUotReadComplete(int result) {
  if (result <= 0) {
    FinishRun(result < 0 ? result : ERR_CONNECTION_CLOSED);
    return;
  }
  uot_read_buffer_.append(read_buffers_[kServer]->data(), result);
  ProcessUotReadBuffer();
}

void NaiveConnection::ProcessUotReadBuffer() {
  while (uot_read_buffer_.size() >= uot_next_read_size_) {
    if (uot_read_state_ == 0) {
      uint8_t atyp = static_cast<uint8_t>(uot_read_buffer_[0]);
      size_t address_len = 0;
      if (atyp == kUotAddressIPv4) {
        address_len = 1 + 4 + 2;
      } else if (atyp == kUotAddressIPv6) {
        address_len = 1 + 16 + 2;
      } else if (atyp == kUotAddressDomain) {
        uot_read_state_ = 1;
        uot_next_read_size_ = 2;
        continue;
      } else {
        FinishRun(ERR_INVALID_RESPONSE);
        return;
      }
      uot_read_state_ = 2;
      uot_next_read_size_ = address_len;
      continue;
    }
    if (uot_read_state_ == 1) {
      size_t domain_len = static_cast<uint8_t>(uot_read_buffer_[1]);
      uot_read_state_ = 2;
      uot_next_read_size_ = 1 + 1 + domain_len + 2;
      continue;
    }
    if (uot_read_state_ == 2) {
      uot_frame_address_ = uot_read_buffer_.substr(0, uot_next_read_size_);
      uot_read_buffer_.erase(0, uot_next_read_size_);
      uot_read_state_ = 3;
      uot_next_read_size_ = 2;
      continue;
    }
    if (uot_read_state_ == 3) {
      uint16_t payload_len = 0;
      if (!ReadUint16(uot_read_buffer_, 0, &payload_len)) {
        FinishRun(ERR_INVALID_RESPONSE);
        return;
      }
      uot_read_buffer_.erase(0, 2);
      uot_read_state_ = 4;
      uot_next_read_size_ = payload_len;
      continue;
    }
    DCHECK_EQ(uot_read_state_, 4);
    std::string payload = uot_read_buffer_.substr(0, uot_next_read_size_);
    uot_read_buffer_.erase(0, uot_next_read_size_);
    if (udp_socket_ && udp_client_endpoint_) {
      std::string packet;
      if (EncodeUotFrameToSocksUdp(uot_frame_address_, payload, &packet)) {
        uot_frame_address_.clear();
        uot_read_state_ = 0;
        uot_next_read_size_ = 1;
        udp_send_buffer_ = base::MakeRefCounted<StringIOBuffer>(packet);
        int rv = udp_socket_->SendTo(
            udp_send_buffer_.get(), packet.size(), *udp_client_endpoint_,
            base::BindOnce(&NaiveConnection::OnUdpFrameWritten,
                           weak_ptr_factory_.GetWeakPtr()));
        if (rv == ERR_IO_PENDING) {
          udp_send_pending_ = true;
          return;
        }
        udp_send_buffer_ = nullptr;
        if (rv < 0) {
          FinishRun(rv);
          return;
        }
      }
    }
    if (uot_read_state_ == 4) {
      uot_frame_address_.clear();
      uot_read_state_ = 0;
      uot_next_read_size_ = 1;
    }
  }
  if (!udp_send_pending_) {
    StartUotRead(uot_next_read_size_ - uot_read_buffer_.size());
  }
}

void NaiveConnection::QueueServerWrite(std::string data) {
  server_write_queue_.push(std::move(data));
  StartServerWrite();
}

void NaiveConnection::StartServerWrite() {
  if (server_write_pending_ || server_write_queue_.empty() ||
      !sockets_[kServer]) {
    return;
  }
  server_write_buffer_ = base::MakeRefCounted<DrainableIOBuffer>(
      base::MakeRefCounted<StringIOBuffer>(server_write_queue_.front()),
      server_write_queue_.front().size());
  server_write_pending_ = true;
  int rv = sockets_[kServer]->Write(
      server_write_buffer_.get(), server_write_buffer_->BytesRemaining(),
      base::BindOnce(&NaiveConnection::OnServerWriteComplete,
                     weak_ptr_factory_.GetWeakPtr()),
      traffic_annotation_);
  if (rv != ERR_IO_PENDING) {
    OnServerWriteComplete(rv);
  }
}

void NaiveConnection::OnServerWriteComplete(int result) {
  if (result < 0) {
    FinishRun(result);
    return;
  }
  server_write_buffer_->DidConsume(result);
  if (server_write_buffer_->BytesRemaining() > 0) {
    int rv = sockets_[kServer]->Write(
        server_write_buffer_.get(), server_write_buffer_->BytesRemaining(),
        base::BindOnce(&NaiveConnection::OnServerWriteComplete,
                       weak_ptr_factory_.GetWeakPtr()),
        traffic_annotation_);
    if (rv != ERR_IO_PENDING) {
      OnServerWriteComplete(rv);
    }
    return;
  }
  server_write_pending_ = false;
  server_write_buffer_ = nullptr;
  server_write_queue_.pop();
  StartServerWrite();
}

void NaiveConnection::FinishRun(int result) {
  if (errors_[kClient] < 0 || errors_[kServer] < 0) {
    return;
  }
  errors_[kClient] = result;
  errors_[kServer] = result;
  if (udp_socket_) {
    udp_socket_->Close();
    udp_socket_.reset();
  }
  Disconnect(kServer);
  client_socket_->Disconnect();
  if (run_callback_) {
    std::move(run_callback_).Run(result);
  }
}

std::optional<PaddingType> NaiveConnection::GetServerPaddingType() const {
  auto* proxy_delegate =
      static_cast<NaiveProxyDelegate*>(session_->context().proxy_delegate);
  DCHECK(proxy_delegate);
  return proxy_delegate->GetProxyChainPaddingType(proxy_info_.proxy_chain());
}

}  // namespace net
