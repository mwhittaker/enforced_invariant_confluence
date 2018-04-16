#! /usr/bin/env bash

set -euo pipefail

usage() {
    echo 'tmux_tail.sh <file>...'
}

main() {
    # http://stackoverflow.com/a/13864829/3187068
    if [[ -z ${TMUX+dummy} ]]; then
        echo "ERROR: you must run this script while in tmux."
        return 1
    fi

    # We need at least 1 argument.
    if [[ "$#" -eq 0 ]]; then
        usage
        exit 1
    fi

    # Create and layout panes.
    tmux new-window -n "tail"
    for ((i = 1; i < "$#"; ++i)); do
        tmux split-window -h -p 99
    done
    tmux select-layout tiled

    # Run tail on each pane.
    args=("$@")
    for ((i = 0; i < "$#"; ++i)); do
        tmux send-keys -t "$i" "tail -f ${args[i]}" C-m
    done
}

main "$@"
