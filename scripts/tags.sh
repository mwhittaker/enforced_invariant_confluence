#! /usr/bin/env bash

set -euo pipefail

main() {
    ctags --language-force=python -R iconfluence
}

main "$@"
