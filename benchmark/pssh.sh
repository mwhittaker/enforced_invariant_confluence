#! /usr/bin/env bash

usage() {
    echo "pssh.sh script"
}

main() {
    if [[ "$#" -ne 1 ]]; then
        usage
        exit 1
    fi

    if [[ ! -f hosts.txt ]]; then
        echo "Create hosts.txt file with EC2 instance hostnames."
    fi

    if [[ ! -f "$HOME/.ssh/aws-ec2.pem" ]]; then
        echo "Move your EC2 key pair to \$HOME/.ssh/aws-ec2.pem"
    fi

    parallel-ssh \
        -x "-i $HOME/.ssh/aws-ec2.pem -A" \
        -l ubuntu \
        -h hosts.txt \
        -t 0 \
        -o out -e err \
        -I < "$1"
}

main "$@"
