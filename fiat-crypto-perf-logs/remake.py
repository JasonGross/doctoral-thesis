#!/usr/bin/env python3
import os, re

dir_path = os.path.dirname(os.path.realpath(__file__))

def parse_lines(lines):
    reg = re.compile(r'^src/Specific/(montgomery|solinas)([0-9]*)_(.*?)_([0-9]+)limbs/(fe[^ \.]*)\.vo (.*)$')
    ret = {}
    for line in lines:
        match = reg.match(line)
        if match:
            kind, bw, prime, nlimbs, op, times = match.groups()
            stats_dict = {}
            for stat in ('real', 'user', 'sys', 'mem'):
                stats_dict[stat] = re.findall(rf'{stat}: ([0-9\.]+)', times)[0]
            ret[(kind, op, int(nlimbs), int(bw), prime)] = stats_dict
    return ret

def make_txt(stats, only_kind=None, only_bw=None, only_op=None):
    return ('bitwidth nlimbs real user sys mem\n' +
            '\n'.join(' '.join((str(bw), str(nlimbs), stat['real'], stat['user'], stat['sys'], stat['mem']))
                      for (kind, op, nlimbs, bw, prime), stat in sorted(stats)
                      if (only_kind is None or kind == only_kind)
                      if (only_bw is None or bw == only_bw)
                      if (only_op is None or op == only_op)) +
            '\n')

if __name__ == '__main__':
    for beforeafter in ('before', 'after'):
        with open(os.path.join(dir_path, f'time-of-build-{beforeafter}-processed.log'), 'r') as f:
            data = parse_lines(f)
        for kind in ('montgomery', 'solinas'):
            for op in ('femul', 'feadd', 'fecarry', 'femul', 'fenz', 'feopp', 'fesquare', 'fesub'):
                txt = make_txt(data.items(), only_kind=kind, only_op=op)
                with open(os.path.join(dir_path, f'{kind}-{op}-{beforeafter}.txt'), 'w') as f:
                    f.write(txt)
