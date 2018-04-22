from collections import defaultdict
import csv
import os
import sys

import matplotlib
import matplotlib.pyplot as plt

EVENTUAL_FMT = {
    'label': 'eventual',
    'marker': 'o',
    'linewidth': 2,
    'markersize': 8,
}
IC_FMT = {
    'label': 'segmented',
    'marker': 's',
    'linewidth': 2,
    'markersize': 8,
}
LIN_FMT = {
    'label': 'linearizable',
    'marker': '^',
    'linewidth': 2,
    'markersize': 8,
}

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

    plt.figure(figsize=(8, 3))
    plt.semilogy(gossip_x, gossip_y, **EVENTUAL_FMT)
    plt.semilogy(segmented_x, segmented_y, **IC_FMT)
    plt.semilogy(paxos_x, paxos_y, **LIN_FMT)
    plt.legend(loc='upper center', ncol=3, bbox_to_anchor=(0.5, 1.2), prop={'size': 12})
    plt.xlabel('Decrement Frequency (fraction of workload)')
    plt.ylabel('Throughput (txns/s)')
    plt.savefig('vary_withdraws.pdf', bbox_inches='tight')
    plt.close()

def plot_vary_segments(data):
    splits = split_data(data)

    gossip_x, gossip_y = splits['gossip']
    segmented_x, segmented_y = splits['segmented_master']
    paxos_x, paxos_y = splits['paxos']

    plt.figure(figsize=(8, 3))
    plt.semilogy(gossip_x, gossip_y, **EVENTUAL_FMT)
    plt.semilogy(segmented_x, segmented_y, **IC_FMT)
    plt.semilogy(paxos_x, paxos_y, **LIN_FMT)
    plt.xlabel('Segment Side Length')
    plt.ylabel('Throughput (txns/s)')
    plt.savefig('vary_segments.pdf', bbox_inches='tight')
    plt.close()

def plot_vary_nodes(data):
    splits = split_data(data)

    gossip_x, gossip_y = splits['gossip']
    segmented_x, segmented_y = splits['segmented_master']
    paxos_x, paxos_y = splits['paxos']

    plt.figure(figsize=(8, 4))
    plt.semilogy(gossip_x, gossip_y, **EVENTUAL_FMT)
    plt.semilogy(segmented_x, segmented_y, **IC_FMT)
    plt.semilogy(paxos_x, paxos_y, **LIN_FMT)
    plt.legend(loc='upper center', ncol=3, bbox_to_anchor=(0.5, 1.15), prop={'size': 12})
    plt.xlabel('Number of Nodes')
    plt.ylabel('Throughput (txns/s)')
    plt.savefig('vary_nodes.pdf', bbox_inches='tight')
    plt.close()

def main():
    if len(sys.argv) != 4:
        print('python plot.py <vary_withdraws.csv> <vary_segments.csv> <vary_nodes.csv>')
        sys.exit(1)

    font = {'family' : 'normal',
            'size'   : 15}
    matplotlib.rc('font', **font)

    plot_vary_withdraws(load_csv(sys.argv[1]))
    plot_vary_segments(load_csv(sys.argv[2]))
    plot_vary_nodes(load_csv(sys.argv[3]))

if __name__ == '__main__':
    main()
