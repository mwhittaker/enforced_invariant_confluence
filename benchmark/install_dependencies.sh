#! /usr/bin/env bash

set -euo pipefail

install_clang() {
    sudo bash -c "echo '' >> /etc/apt/sources.list"
    sudo bash -c "echo '# http://apt.llvm.org/' >> /etc/apt/sources.list"
    sudo bash -c "echo 'deb http://apt.llvm.org/trusty/ llvm-toolchain-trusty-4.0 main' >> /etc/apt/sources.list"
    sudo bash -c "echo 'deb-src http://apt.llvm.org/trusty/ llvm-toolchain-trusty-4.0 main' >> /etc/apt/sources.list"
    wget -O - http://apt.llvm.org/llvm-snapshot.gpg.key | sudo apt-key add -
    sudo apt-get -y update

    sudo apt-get install -y \
        clang-4.0 clang-format-4.0 clang-tidy-4.0 lldb-4.0
    sudo ln -s "$(which clang-4.0)" /usr/bin/clang
    sudo ln -s "$(which clang++-4.0)" /usr/bin/clang++
    sudo ln -s "$(which clang-format-4.0)" /usr/bin/clang-format
    sudo ln -s "$(which clang-tidy-4.0)" /usr/bin/clang-tidy
    sudo ln -s "$(which lldb-4.0)" /usr/bin/lldb
    sudo ln -s "$(which lldb-server-4.0)" /usr/bin/lldb-server
}

install_glog() {
    sudo apt-get install -y libgoogle-glog-dev
}

install_protobuf() {
    sudo add-apt-repository ppa:maarten-fonville/protobuf -y
    sudo apt-get update -y
    sudo apt-get install -y libprotobuf-dev protobuf-compiler
}

install_libuv() {
    sudo apt-get install -y libtool m4 automake
    git clone https://github.com/libuv/libuv.git
    cd libuv
    sh autogen.sh
    ./configure
    make
    sudo make install
}

main() {
    sudo apt-get update -y
    sudo apt-get upgrade -y
    sudo apt-get install -y pkg-config exuberant-ctags
    install_clang
    install_glog
    install_protobuf
    install_libuv
}

main "$@"
