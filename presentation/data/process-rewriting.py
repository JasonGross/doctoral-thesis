#!/usr/bin/env python3
import argparse
import sys, os, os.path
import csv
import re
import math

DIR = os.path.dirname(os.path.realpath(__file__))

def readfile(f):
    freader = csv.DictReader(f)
    fields = freader.fieldnames
    rows = list(freader)
    f.close()
    return fields, rows

def make_data(data):
    ret = {}
    all_keys = set()
    for row in data:
        if row['prime'] not in ret.keys(): ret[row['prime']] = {'prime_str': row['prime_str']}
        descr = ('%(kind)s x%(bitwidth)s %(descr1)s %(descr2)s %(index)s' % row).strip()
        ret[row['prime']][descr] = row['user'] if 'native' not in row['descr2'] else row['real']
        all_keys.add(descr)
    return all_keys, ret

def write_data(f, all_keys, data):
    fwriter = csv.writer(f)
    all_keys = ['prime_str'] + list(sorted(all_keys))
    primes = list(sorted(data.keys(), key=int))
    fwriter.writerow(['prime', 'prime num'] + all_keys)
    for p in primes:
        fwriter.writerow(['p' + p, int(p)] + [data[p].get(i) for i in all_keys])
    f.close()

if __name__ == '__main__':
    fields, data = readfile(open(os.path.join(DIR, 'fiat-crypto-POPL-2020-rewriting-perf.csv'), 'r'))
    all_keys, new_data = make_data(data)
    write_data(open(os.path.join(DIR, 'fiat-crypto-POPL-2020-rewriting-perf-cols.csv'), 'w'), all_keys, new_data)
