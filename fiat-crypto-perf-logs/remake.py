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
            ret[(kind, int(bw), op, int(nlimbs), prime)] = stats_dict
    return ret

def make_txt(stats):
    return ('kind bitwidth op nlimbs prime real user sys mem\n' +
            '\n'.join(' '.join((kind, str(bw), op, str(nlimbs), prime, stat['real'], stat['user'], stat['sys'], stat['mem']))
                      for (kind, bw, op, nlimbs, prime), stat in stats) +
            '\n')

if __name__ == '__main__':
    for beforeafter in ('before', 'after'):
        with open(os.path.join(dir_path, f'time-of-build-{beforeafter}-processed.log'), 'r') as f:
            data = parse_lines(f)
        txt = make_txt(data.items())
        with open(os.path.join(dir_path, f'time-of-build-{beforeafter}.txt'), 'w') as f:
            f.write(txt)
