#!/usr/bin/env bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
cd "$DIR"

for beforeafter in before after
do
    INFILE=time-of-build-$beforeafter-processed.log
    for kind in montgomery solinas
    do
        for op in femul feadd fecarry femul fenz feopp fesquare fesub
        do
            for timekind in real user sys mem
            do
                OUTFILE=${kind}-${op}-${beforeafter}-${timekind}.txt
                echo "$OUTFILE"
                cat "$INFILE" | grep "^src/Specific/$kind[^ ]*/$op\.vo" | sed "s/[^ ]*_\([0-9]*\)limbs.*$timekind: \([0-9\.]*\)[ ),].*/\1 \2/g" | sort -h > $OUTFILE
            done
        done
    done
done
