#! /usr/bin/env bash

set -euo pipefail

main() {
    mypy iconfluence --ignore-missing-imports
    mypy examples --ignore-missing-imports
}

main "$@"
