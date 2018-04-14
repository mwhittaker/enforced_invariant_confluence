#include "object.h"

#include "glog/logging.h"

std::ostream& operator<<(std::ostream& out, const SyncStatus status) {
  switch (status) {
    case SyncStatus::EXECUTED_LOCALLY: {
      out << "EXECUTED_LOCALLY";
      break;
    }
    case SyncStatus::REQUIRES_SYNC: {
      out << "REQUIRES_SYNC";
      break;
    }
    default: { LOG(FATAL) << "Unrecognized SyncStatus."; }
  }
  return out;
}

SyncStatus Object::ExecTxnSegmented(const std::string& txn,
                                    std::string* reply) {
  *reply = ExecTxn(txn);
  return SyncStatus::EXECUTED_LOCALLY;
}
