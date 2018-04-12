#include "object.h"

SyncStatus Object::ExecTxnSegmented(const std::string& txn,
                                    std::string* reply) {
  *reply = ExecTxn(txn);
  return SyncStatus::EXECUTED_LOCALLY;
}
