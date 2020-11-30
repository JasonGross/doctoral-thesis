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

def add_old_pipeline_data(all_keys, data, lines):
    matches = re.findall(r'src/Specific/(montgomery|solinas)([0-9]*)_([^_]*)_([0-9]*)limbs/femul.vo [^)]*?user: ([0-9\.]*)[^\)]*', '\n'.join(sorted(lines.split('\n'))))
    seen_keys = {}
    for kind, bitwidth, p, limbc, utime in matches:
        p_str = p.replace('e', '^').replace('m', '-').replace('p', '+')
        p = str(eval(p_str.replace('^', '**')))
        if p not in data.keys(): raise Exception('Could not find %s' % p_str)
        descr1 = f'{kind} x{bitwidth} old pipeline'
        seen_keys[descr1] = seen_keys.get(descr1, -1) + 1
        descr = f'{descr1} ({seen_keys[descr1]})'
        #data[p]


    #src/Specific/montgomery64_2e416m2e208m1_7limbs/femul.vo (real: 856.16, user: 850.25, sys: 5.88, mem: 15530700 ko)\n

if __name__ == '__main__':
    fields, data = readfile(open(os.path.join(DIR, 'fiat-crypto-POPL-2020-rewriting-perf.csv'), 'r'))
    all_keys, new_data = make_data(data)
    write_data(open(os.path.join(DIR, 'fiat-crypto-POPL-2020-rewriting-perf-cols.csv'), 'w'), all_keys, new_data)
    with open(os.path.join(DIR, 'time-of-build-8.11.1-processed.log'), 'r') as f:
        old_pipeline_lines = f.read()
    add_old_pipeline_data(all_keys, new_data, old_pipeline_lines)
