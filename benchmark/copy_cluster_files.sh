#! /usr/bin/env bash

usage() {
    echo "./copy_cluster_files.sh"
}

main() {
    if [[ "$#" -ne 0 ]]; then
        usage
        exit 1
    fi

    if [[ ! -f benchmark_server_cluster.txt ]]; then
        echo "Create benchmark_server_cluster.txt."
        exit 1
    fi

    if [[ ! -f server_cluster.txt ]]; then
        echo "Create server_cluster.txt."
        exit 1
    fi

    if [[ ! -f benchmark_client_cluster.txt ]]; then
        echo "Create benchmark_client_cluster.txt."
        exit 1
    fi

    ./pscp.sh benchmark_server_cluster.txt /home/ubuntu/benchmark_server_cluster.txt
    ./pscp.sh server_cluster.txt /home/ubuntu/server_cluster.txt
    ./pscp.sh benchmark_client_cluster.txt /home/ubuntu/benchmark_client_cluster.txt
}

main "$@"
