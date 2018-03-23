#! /usr/bin/env bash

set -euo pipefail

boxed() {
    local -r msg="| $1 |"
    echo "$msg" | sed 's/./=/g'
    echo "$msg"
    echo "$msg" | sed 's/./=/g'
}

main() {
    local -r num_todos="$(grep -rn 'TODO' $(find . -name '*.py') | wc -l)"
    if [[ "$num_todos" -ne 0 ]]; then
        boxed "There are $num_todos TODOs in the code."
        grep -rn 'TODO' $(find . -name '*.py')
    fi
}

main "$@"
