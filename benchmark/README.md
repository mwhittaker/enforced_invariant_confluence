# Benchmarks

1. Launch EC2 instances with `./launch_ec2_instances.sh`.
2. After the EC2 instances have been launched, create the `hosts.txt` and
   `*_cluster.txt` files with `./create_cluster_files.sh`
3. Run `./terminals.sh` to confirm that we want to connect.
4. Copy the `*_cluster.txt` files over to the servers with
   `./copy_cluster_files.sh`.
5. Delete `out/` and `err/` and install everything on the cluster with
   `./pssh.sh clone_install_build_launch.sh`. To inspect the stdout and stderr
   of the servers, you can run `./tmux_tail.sh out/*` and `./tmux_tail.sh
   err/*`.
