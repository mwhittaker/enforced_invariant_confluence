#! /usr/bin/env bash

set -euo pipefail

usage() {
    echo './terminals.sh'
}

main() {
    # http://stackoverflow.com/a/13864829/3187068
    if [[ -z ${TMUX+dummy} ]]; then
        echo "ERROR: you must run this script while in tmux."
        return 1
    fi

    if [[ ! -f hosts.txt ]]; then
        echo "Create hosts.txt file with EC2 instance hostnames."
    fi

    if [[ ! -f "$HOME/.ssh/aws-ec2.pem" ]]; then
        echo "Move your EC2 key pair to \$HOME/.ssh/aws-ec2.pem"
    fi

    if [[ "$#" -ne 0 ]]; then
        usage
        exit 1
    fi

    # Read hosts.txt into hosts.
    hosts=()
    while read host; do
        hosts+=("$host")
    done < hosts.txt

    # Construct ssh commands.
    ssh_cmds=()
    for host in "${hosts[@]}"; do
        ssh_cmds+=("ssh -i $HOME/.ssh/aws-ec2.pem -A ubuntu@$host")
    done

    # Create and layout panes.
    tmux new-window -n "terminals"
    for ((i = 1; i < "${#ssh_cmds[@]}"; ++i)); do
        tmux split-window -h -p 99
    done
    tmux select-layout tiled

    # Run ssh command on each pane.
    for ((i = 0; i < "${#ssh_cmds[@]}"; ++i)); do
        tmux send-keys -t "$i" "${ssh_cmds[i]}" C-m
    done
}

main
