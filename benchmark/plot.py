from collections import defaultdict
import csv
import os
import sys

import matplotlib.pyplot as plt

def load_csv(filename):
    with open(filename, 'r') as f:
        reader = csv.reader(f, delimiter=',')
        return [(row[0], float(row[1]), float(row[2])) for row in reader]

def split_data(data):
    splits = defaultdict(lambda: ([], []))
    for (server_type, x, y) in data:
        splits[server_type][0].append(x)
        splits[server_type][1].append(y)
    return splits

def plot_vary_withdraws(data):
    splits = split_data(data)

    gossip_x, gossip_y = splits['gossip']
    segmented_x, segmented_y = splits['segmented_master']
    paxos_x, paxos_y = splits['paxos']

    plt.figure()
    plt.semilogy(gossip_x, gossip_y, label='eventual', marker='o')
    plt.semilogy(segmented_x, segmented_y, label='invariant confluent', marker='s')
    plt.semilogy(paxos_x, paxos_y, label='linearizable', marker='^')
    plt.legend()
    plt.xlabel('Fraction Withdrawals')
    plt.ylabel('Throughput (txns/s)')
    plt.savefig('vary_withdraws.pdf')
    plt.close()

def plot_vary_segments(data):
    splits = split_data(data)

    gossip_x, gossip_y = splits['gossip']
    segmented_x, segmented_y = splits['segmented_master']
    paxos_x, paxos_y = splits['paxos']

    plt.figure()
    plt.semilogy(gossip_x, gossip_y, label='eventual', marker='o')
    plt.semilogy(segmented_x, segmented_y, label='invariant confluent', marker='s')
    plt.semilogy(paxos_x, paxos_y, label='linearizable', marker='^')
    plt.legend()
    plt.xlabel('Segment Side Length')
    plt.ylabel('Throughput (txns/s)')
    plt.savefig('vary_segments.pdf')
    plt.close()

def plot_vary_nodes(data):
    splits = split_data(data)

    gossip_x, gossip_y = splits['gossip']
    segmented_x, segmented_y = splits['segmented_master']
    paxos_x, paxos_y = splits['paxos']

    plt.figure()
    plt.semilogy(gossip_x, gossip_y, label='eventual', marker='o')
    plt.semilogy(segmented_x, segmented_y, label='invariant confluent', marker='s')
    plt.semilogy(paxos_x, paxos_y, label='linearizable', marker='^')
    plt.legend()
    plt.xlabel('Number of Nodes')
    plt.ylabel('Throughput (txns/s)')
    plt.savefig('vary_nodes.pdf')
    plt.close()

def main():
    if len(sys.argv) != 4:
        print('python plot.py <vary_withdraws.csv> <vary_segments.csv> <vary_nodes.csv>')
        sys.exit(1)

    plot_vary_withdraws(load_csv(sys.argv[1]))
    plot_vary_segments(load_csv(sys.argv[2]))
    plot_vary_nodes(load_csv(sys.argv[3]))

if __name__ == '__main__':
    main()
