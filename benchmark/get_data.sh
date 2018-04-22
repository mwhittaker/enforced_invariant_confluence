#! /usr/bin/env bash

set -euo pipefail

usage() {
    echo "get_data.sh"
}

main() {
    if [[ "$#" -ne 0 ]]; then
        usage
        exit 1
    fi

    if [[ ! -f hosts.txt ]]; then
        echo "Create hosts.txt file with EC2 instance hostnames."
    fi

    if [[ ! -f "$HOME/.ssh/aws-ec2.pem" ]]; then
        echo "Move your EC2 key pair to \$HOME/.ssh/aws-ec2.pem"
    fi

    hosts=()
    while read host; do
        hosts+=("$host")
    done < hosts.txt

    for host in "${hosts[@]}"; do
        if [[ -e "$host" ]]; then
            echo "Delete $host directory."
            exit 1
        fi
        mkdir "$host"

        scp \
            -r \
            -i ~/.ssh/aws-ec2.pem \
            "ubuntu@$host:/home/ubuntu/mpc-bootstrap/data/Nov*" \
            "$host"

        for d in "$host"/*; do
            mv $d $host/${host}_$(basename $d)
        done
    done
}

main
