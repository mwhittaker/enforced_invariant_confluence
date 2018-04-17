#! /usr/bin/env bash

set -euo pipefail

main() {
    # Clone the repo and install dependencies.
    if ! [[ -d enforced_invariant_confluence ]]; then
        echo "enforced_invariant_confluence doesn't exist"
        sudo apt-get install -y git
        # Enable us to clone github repos without user interaction
        # (https://serverfault.com/a/641392).
        ssh-keyscan github.com >> ~/.ssh/known_hosts
        git clone git@github.com:mwhittaker/enforced_invariant_confluence
        bash enforced_invariant_confluence/benchmark/install_dependencies.sh
    fi

    cd enforced_invariant_confluence/lucy
    git pull
    make DEBUG=0

    if tmux has-session -t iconfluence &> /dev/null; then
        tmux kill-session -t iconfluence
    fi

    tmux -2 new-session -d -s iconfluence
    tmux rename-window -t 0 server
    tmux new-window -n client_1
    tmux new-window -n client_2
    tmux new-window -n client_3

    private_ip="$(hostname -I)"
    echo "private_ip = $private_ip"
    # Launch the servers, but only if we're not the master.
    if grep $private_ip $HOME/benchmark_client_cluster.txt &> /dev/null; then
        echo "STARTING SERVERS"
        server_index="$(grep -n $private_ip ~/benchmark_server_cluster.txt | cut -d : -f 1)"
        server_index="$((server_index - 1))"
        client_1_index="$((server_index * 3))"
        client_2_index="$((client_1_index + 1))"
        client_3_index="$((client_1_index + 2))"

        echo "server_index = $server_index"
        echo "client_1_index = $client_1_index"
        echo "client_2_index = $client_2_index"
        echo "client_3_index = $client_3_index"

        tmux send-keys -t iconfluence:server.0 \
            'LD_LIBARY_PATH="$LD_LIBRARY_PATH:/usr/local/lib" GLOG_logtostderr=1 GLOG_v=0 ./benchmark_server_main ~/benchmark_server_cluster.txt ~/server_cluster.txt '"$server_index" C-m
        tmux send-keys -t iconfluence:client_1.0 \
            'LD_LIBARY_PATH="$LD_LIBRARY_PATH:/usr/local/lib" GLOG_logtostderr=1 GLOG_v=0 ./benchmark_client_main ~/benchmark_client_cluster.txt ~/server_cluster.txt '"$client_1_index" C-m
        tmux send-keys -t iconfluence:client_2.0 \
            'LD_LIBARY_PATH="$LD_LIBRARY_PATH:/usr/local/lib" GLOG_logtostderr=1 GLOG_v=0 ./benchmark_client_main ~/benchmark_client_cluster.txt ~/server_cluster.txt '"$client_2_index" C-m
        tmux send-keys -t iconfluence:client_3.0 \
            'LD_LIBARY_PATH="$LD_LIBRARY_PATH:/usr/local/lib" GLOG_logtostderr=1 GLOG_v=0 ./benchmark_client_main ~/benchmark_client_cluster.txt ~/server_cluster.txt '"$client_3_index" C-m
    else
        echo "NOT STARTING SERVERS"
    fi
}

main "$@"
