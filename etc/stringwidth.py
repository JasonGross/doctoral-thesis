#!/usr/bin/env python
from __future__ import print_function
import sys, string, math
# https://stackoverflow.com/a/16008023/377022

def getApproximateArialStringWidth(st):
    size = 0 # in milinches
    for s in st:
        if s in 'lij|\' ': size += 37
        elif s in '![]fI.,:;/\\t': size += 50
        elif s in '`-(){}r"': size += 60
        elif s in '*^zcsJkvxy': size += 85
        elif s in 'aebdhnopqug#$L+<>=?_~FZT' + string.digits: size += 95
        elif s in 'BSPEAKVXY&UwNRCHD': size += 112
        elif s in 'QGOMm%W@': size += 135
        else: size += 50
    return size * 6 / 1000.0 # Convert to picas = 1/12 pt = 1em


if __name__ == '__main__':
    widths = (getApproximateArialStringWidth(line.strip('\n')) for line in sys.stdin.readlines())
    transform = (lambda x: int(math.ceil(x))) if '--int' in sys.argv[1:] else (lambda x: x)
    if '--max' in sys.argv[1:]:
        print(transform(max(widths)), end='')
    else:
        for width in widths: print(transform(width))
