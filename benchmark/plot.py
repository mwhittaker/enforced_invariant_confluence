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
        return [(row[0], float(row[1]), float(row[2]), float(row[3]))
                for row in reader]

def extract_bank_account_data(data):
    records = []
    for (server_type, num_servers, fraction_withdraw, throughput) in data:
        records.append({
            'server_type': server_type,
            'num_servers': num_servers,
            'fraction_withdraw': fraction_withdraw,
            'throughput': throughput,
        })
    return records

def partition_by_server_type(records):
    gossip = []
    segmented_master = []
    paxos = []
    for r in records:
        if r['server_type'] == 'gossip':
            gossip.append(r)
        elif r['server_type'] == 'segmented_master':
            segmented_master.append(r)
        elif r['server_type'] == 'paxos':
            paxos.append(r)
        else:
            raise ValueError(r['server_type'])
    return gossip, segmented_master, paxos

def plot_bank_account(data):
    records = extract_bank_account_data(data)
    num_servers_domain = sorted(set(r['num_servers'] for r in records))
    frac_withdraw_domain = sorted(set(r['fraction_withdraw'] for r in records))

    # First, we plot the throughput (y-axis) vs fraction withdraw (x-axis) for
    # each number of servers.
    def filter_num_servers_sort_fraction(records, n):
        filtered = [r for r in records if r['num_servers'] == n]
        ordered = sorted(filtered, key=lambda r: r['fraction_withdraw'])
        xs = [r['fraction_withdraw'] for r in ordered]
        ys = [r['throughput'] for r in ordered]
        return xs, ys

    for n in num_servers_domain:
        gossip, master, paxos = partition_by_server_type(records)
        gossip_xs, gossip_ys = filter_num_servers_sort_fraction(gossip, n)
        master_xs, master_ys = filter_num_servers_sort_fraction(master, n)
        paxos_xs, paxos_ys = filter_num_servers_sort_fraction(paxos, n)

        plt.figure(figsize=(8, 3))
        plt.semilogy(gossip_xs, gossip_ys, **EVENTUAL_FMT)
        plt.semilogy(paxos_xs, paxos_ys, **LIN_FMT)
        plt.semilogy(master_xs, master_ys, **IC_FMT)
        plt.legend(loc='upper center', ncol=3, bbox_to_anchor=(0.5, 1.2), prop={'size': 12})
        plt.xlabel('Decrement Frequency (fraction of workload)')
        plt.ylabel('Throughput (txns/s)')
        plt.savefig(f'throughput_vs_fraction_{n}.pdf', bbox_inches='tight')
        plt.close()

    # Next, we plot the throughput (y-axis) vs number of nodes (x-axis) for
    # each fraction of withdraws.
    def filter_fraction_sort_num_servers(records, f):
        filtered = [r for r in records if r['fraction_withdraw'] == f]
        ordered = sorted(filtered, key=lambda r: r['num_servers'])
        xs = [r['num_servers'] for r in ordered]
        ys = [r['throughput'] for r in ordered]
        return xs, ys

    for f in frac_withdraw_domain:
        gossip, master, paxos = partition_by_server_type(records)
        gossip_xs, gossip_ys = filter_fraction_sort_num_servers(gossip, f)
        master_xs, master_ys = filter_fraction_sort_num_servers(master, f)
        paxos_xs, paxos_ys = filter_fraction_sort_num_servers(paxos, f)

        plt.figure(figsize=(8, 4))
        plt.semilogy(gossip_xs, gossip_ys, **EVENTUAL_FMT)
        plt.semilogy(paxos_xs, paxos_ys, **LIN_FMT)
        plt.semilogy(master_xs, master_ys, **IC_FMT)
        plt.legend(loc='upper center', ncol=3, bbox_to_anchor=(0.5, 1.15), prop={'size': 12})
        plt.xlabel('Number of Nodes')
        plt.ylabel('Throughput (txns/s)')
        plt.savefig(f'throughput_vs_num_nodes_{f}.pdf', bbox_inches='tight')
        plt.close()

    # Finally, we plot the throughput (y-axis) vs number of nodes (x-axis) for
    # a couple different fraction of withdraws on the same plot.
    gossip, master, paxos = partition_by_server_type(records)
    gossip_xs, gossip_ys = filter_fraction_sort_num_servers(gossip, 0)
    paxos_xs, paxos_ys = filter_fraction_sort_num_servers(paxos, 0)
    fractions = [0.01, 0.05, 0.2, 0.5]
    master_data = {f: filter_fraction_sort_num_servers(master, f)
                   for f in fractions}
    markers = {
        0.01: 's',
        0.05: 'p',
        0.2: '*',
        0.5: 'x',
    }

    plt.figure(figsize=(8, 4))
    plt.semilogy(gossip_xs, gossip_ys, **EVENTUAL_FMT)
    plt.semilogy(paxos_xs, paxos_ys, **LIN_FMT)
    for f, (xs, ys) in master_data.items():
        fmt = dict(IC_FMT.items())
        del fmt['label']
        del fmt['marker']
        plt.semilogy(xs, ys, marker=markers[f], label=f'segmented ({f})', **fmt)
    plt.legend(loc='upper center', ncol=3, bbox_to_anchor=(0.5, 1.25), prop={'size': 12})
    plt.xlabel('Number of Nodes')
    plt.ylabel('Throughput (txns/s)')
    plt.savefig(f'throughput_vs_num_nodes_multi.pdf', bbox_inches='tight')
    plt.close()

def main():
    if len(sys.argv) != 2:
        print('python plot.py <bank_account.csv>')
        sys.exit(1)

    font = {'family': 'normal', 'size': 15}
    matplotlib.rc('font', **font)
    plot_bank_account(load_csv(sys.argv[1]))

if __name__ == '__main__':
    main()
