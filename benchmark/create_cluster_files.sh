#! /usr/bin/env bash

usage() {
    echo "./create_cluster_files.sh"
}

main() {
    if [[ "$#" -ne 0 ]]; then
        usage
        exit 1
    fi

    python create_cluster_files.py <(aws ec2 describe-instances)
}

main "$@"
