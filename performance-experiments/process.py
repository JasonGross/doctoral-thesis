#!/usr/bin/env python3
import argparse
import sys, os, os.path
import csv
import re
import math

parser = argparse.ArgumentParser()
parser.add_argument('-o', '--output-file', dest='outfile', type=argparse.FileType('w'),
                    default=sys.stdout,
                    help="output file name")
parser.add_argument('--txts', action='store_true',
                    help="also emit .txt files for each column in the csv")
parser.add_argument('kind', metavar='KIND', type=str,
                    help="the kind of output")
parser.add_argument('infile', metavar='INFILE.csv', type=argparse.FileType('r'),
                    help='input log files')

def readfile(f):
    freader = csv.DictReader(f)
    fields = freader.fieldnames
    rows = list(freader)
    f.close()
    return fields, rows

def process_rows(data, kind):
    def remap(new, old, row):
        if isinstance(old, str):
            return (new, row[old])
        elif callable(old):
            return (new, old(row))
        else:
            raise Exception('Invalid non-str-non-callable: %s (for %s)' % (repr(old), new))
    rows = [row for row in data if row['param kind'] == kind]
    kind_map = {
        'conj_True_repeat_constructor': {
            'keymap': [('type size', 'param n'),
                       ('repeat constructor', 'repeat-constructor user')],
            'key'   : (lambda row: int(row['type size'])) },
        'conj_True_uconstr': {
            'keymap': [('type size', 'param n'),
                       ('typechecking', 'to_constr user')],
            'key'   : (lambda row: int(row['type size'])) },
        'conj_True_ltac2': {
            'keymap': [('type size', 'param n'),
                       ('typechecking', 'typecheck user')],
            'key'   : (lambda row: int(row['type size'])) },
        'LiftLetsMap': {
            'keymap': [('list length', 'param n'),
                       ('iteration count', 'param m'),
                       ('term size', (lambda row: int(row['param n']) * int(row['param m']))),
                       ('Rewrite_for', 'Rewrite_for_gen user'),
                       ('rewriting', 'rewriting user'),
                       ('rewriting (vm only)', 'vm_compute_and_unify_in_rewrite user'),
                       ('rewrite_strat(topdown,bottomup)', 'rewrite_strat(topdown,bottomup) user'),
                       ('rewrite_strat(bottomup,bottomup)', 'rewrite_strat(bottomup,bottomup) user'),
                       ('cps+vm_compute', 'cps+vm_compute user'),
                       ('setoid_rewrite', 'setoid_rewrite user')],
            'key'   : (lambda row: row['term size']) },
        'Plus0Tree': {
            'keymap': [('tree depth', 'param n'),
                       ('extra +0s per node', 'param m'),
                       ('term size', (lambda row: (int(row['param m']) + 1) * (2 ** (int(row['param n']) + 1)) - int(row['param m']))),
                       ('term size+29', (lambda row: (int(row['param m']) + 1 + 29) * (2 ** (int(row['param n']) + 1)) - int(row['param m']))),
                       ('Rewrite_for', 'Rewrite_for_gen user'),
                       ('rewriting', 'rewriting user'),
                       ('rewriting (vm only)', 'vm_compute_and_unify_in_rewrite user'),
                       ('cbv;rewrite!', 'cbv;rewrite! user'),
                       ('cbv;setoid_rewrite', 'cbv;setoid_rewrite user'),
                       ('cbv;rewrite_strat(topdown)', 'cbv;rewrite_strat(topdown) user'),
                       ('cbv;rewrite_strat(bottomup)', 'cbv;rewrite_strat(bottomup) user')],
            'key'   : (lambda row: row['term size']) },
        'SieveOfEratosthenes': {
            'keymap': [('n', 'param n'),
                       ('Rewrite_for', 'Rewrite_for_gen user'),
                       ('rewriting', 'rewriting user'),
                       ('rewriting (vm only)', 'vm_compute_and_unify_in_rewrite user'),
                       ('cbv', 'cbv user'),
                       ('lazy', 'lazy user'),
                       ('vm_compute', 'vm_compute user'),
                       ('native(1)(real)', 'native_compute(1) real'),
                       ('native(2)(real)', 'native_compute(2) real'),
                       ('cbn', 'cbn user'),
                       ('simpl', 'simpl user')],
            'key'   : (lambda row: int(row['n'])) },
        'UnderLetsPlus0': {
            'keymap': [('n', 'param n'),
                       ('Rewrite_for', 'Rewrite_for_gen user'),
                       ('rewriting', 'rewriting user'),
                       ('rewriting (vm only)', 'vm_compute_and_unify_in_rewrite user'),
                       ('cbv;rewrite_strat(bottomup)', 'cbv;rewrite_strat(bottomup) user'),
                       ('cbv;rewrite_strat(topdown)', 'cbv;rewrite_strat(topdown) user'),
                       ('cbv;setoid_rewrite', 'cbv;setoid_rewrite user')],
            'key'   : (lambda row: int(row['n'])) }
    }
    if kind not in kind_map.keys():
        raise Exception('Invalid kind: %s; expected one of %s' % (kind, ', '.join(sorted(kind_map.keys()))))
    keymap, key = kind_map[kind]['keymap'], kind_map[kind]['key']
    return tuple(k for k, k_old in keymap), sorted([dict(remap(k, k_old, row) for k, k_old in keymap) for row in rows], key=key)

def emit_output(f, fields, rows, kind, txts=False):
    fname, fext = os.path.splitext(f.name)
    rows = list(rows)
    fwriter = csv.DictWriter(f, fields, lineterminator="\n")
    fwriter.writeheader()
    fwriter.writerows(rows)
    f.close()

    if txts:
        def get_lines(k, size_field, only_if=(lambda row: True)):
            return ['%d %s' % (int(row[size_field]), row[k]) for row in rows if k in row.keys() and only_if(row) and row[k] not in (None, '')]
        def writef(extra, k, lines):
            with open(fname + '%s-%s.txt' % (extra, k.replace(' ', '-').replace('_', '-')), 'w') as f_txt:
                f_txt.write('\n'.join(lines))
        k_good = (lambda k: k not in ('n', 'm', 'type size', 'term size', 'list length', 'iteration count', 'extra +0s per node', 'tree depth') and not k.startswith('term size'))
        size_fields = ['term size' if 'term size' in fields else 'type size' if 'type size' in fields else 'n']
        size_fields.extend(k for k in fields if k.startswith('term size+'))
        for size_field in size_fields:
            extra = ''
            if size_field.startswith('term size+'): extra = size_field[len('term size'):]
            for k in fields:
                if k_good(k):
                    lines = get_lines(k, size_field)
                    writef(extra, k, lines)
        if kind == 'Plus0Tree':
            for n in range(1, 10):
                for k in fields:
                    if k_good(k):
                        lines = get_lines(k, 'extra +0s per node', only_if=(lambda row: int(row['tree depth']) == n))
                        writef('-only-n-%d' % n, k, lines)
            for m in range(1, 4):
                for k in fields:
                    if k_good(k):
                        lines = get_lines(k, 'tree depth', only_if=(lambda row: int(row['extra +0s per node']) == m))
                        writef('-only-m-%d' % m, k, lines)

if __name__ == '__main__':
    args = parser.parse_args()
    fields, data = readfile(args.infile)
    fields, rows = process_rows(data, args.kind)
    emit_output(args.outfile, fields, rows, args.kind, txts=args.txts)
