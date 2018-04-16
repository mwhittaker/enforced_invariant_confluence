#! /usr/bin/env bash

usage() {
    echo "pscp.sh local remote"
}

main() {
    if [[ "$#" -ne 2 ]]; then
        usage
        exit 1
    fi
    local -r local_file="$1"
    local -r remote_file="$2"

    if [[ ! -f hosts.txt ]]; then
        echo "Create hosts.txt file with EC2 instance hostnames."
        exit 1
    fi

    if [[ ! -f "$HOME/.ssh/aws-ec2.pem" ]]; then
        echo "Move your EC2 key pair to \$HOME/.ssh/aws-ec2.pem"
        exit 1
    fi

    parallel-scp \
        -O "IdentityFile=$HOME/.ssh/aws-ec2.pem" \
        -l ubuntu \
        -h hosts.txt \
        -o out -e err \
        "$local_file" \
        "$remote_file"
}

main "$@"
