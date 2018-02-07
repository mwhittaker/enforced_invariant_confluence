#! /usr/bin/env bash

set -euo pipefail

main() {
    pylint iconfluence --errors-only
}

main "$@"
