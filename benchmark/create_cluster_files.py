import sys
import json

def usage():
    return "python create_cluster_files.py <(aws ec2 describe-instances)"

def main():
    if len(sys.argv) != 2:
        print(usage())
        sys.exit(1)

    with open(sys.argv[1], "r") as f:
        data = json.loads(f.read())

    public_ips = []
    private_ips = []
    for reservation in data["Reservations"]:
        for instance in reservation["Instances"]:
            if instance["State"]["Name"] == "running":
                public_ips.append(instance["PublicIpAddress"])

                if ("Tags" in instance and
                    {"Key": "Name", "Value": "master"} in instance["Tags"]):
                    # This is the master.
                    print("Master is at {}.".format(instance["PublicIpAddress"]))
                    pass
                else:
                    private_ips.append(instance["PrivateIpAddress"])

    with open("hosts.txt", "w") as f:
        for public_ip in public_ips:
            f.write(public_ip + '\n')

    with open("benchmark_server_cluster.txt", "w") as f:
        for private_ip in private_ips:
            f.write('host_port {{ host: "{}" port: 7000 }}\n'.format(private_ip))

    with open("server_cluster.txt", "w") as f:
        for private_ip in private_ips:
            f.write('host_port {{ host: "{}" port: 8000 }}\n'.format(private_ip))

    with open("benchmark_client_cluster.txt", "w") as f:
        for private_ip in private_ips:
            f.write('host_port {{ host: "{}" port: 8000 }}\n'.format(private_ip))
            f.write('host_port {{ host: "{}" port: 8001 }}\n'.format(private_ip))
            f.write('host_port {{ host: "{}" port: 8002 }}\n'.format(private_ip))

if __name__ == '__main__':
    main()
