#! /usr/bin/env bash

set -euo pipefail

main() {
    mypy iconfluence --ignore-missing-imports
}

main "$@"
