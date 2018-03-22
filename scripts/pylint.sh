#! /usr/bin/env bash

set -euo pipefail

main() {
    pylint iconfluence --errors-only
    pylint examples --errors-only
}

main "$@"
