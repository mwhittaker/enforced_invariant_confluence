#include "object.h"

SyncStatus Object::RunSegmented(const std::string& txn, std::string* reply) {
  *reply = Run(txn);
  return SyncStatus::EXECUTED_LOCALLY;
}
