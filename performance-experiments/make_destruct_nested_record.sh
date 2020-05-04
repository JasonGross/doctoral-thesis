#!/usr/bin/env bash
# USAGE: $0 SIZE

case "$1" in
    SuperFast)
        vs="$(seq 1 1 200)"
        ;;
    Fast)
        vs="$(seq 205 5 450) $(seq 500 100 1500)"
        ;;
    Medium)
        vs="$(seq 1600 100 2000)"
        ;;
    Slow)
        vs=""
        ;;
    VerySlow)
        vs=""
        ;;
    * )
        echo "Invalid argument '$1'" >&2
        exit 1
esac

FIELDS_SO_FAR=""
last_i=0
echo 'Unset Boolean Equality Schemes.'
echo 'Unset Case Analysis Schemes.'
echo 'Unset Decidable Equality Schemes.'
echo 'Unset Elimination Schemes.'
echo 'Unset Primitive Projections.'
echo 'Unset Rewriting Schemes.'
echo 'Unset Nonrecursive Elimination Schemes.'
for i in ${vs}; do
    for j in $(seq $((${last_i}+1)) $i); do
        FIELDS_SO_FAR="${FIELDS_SO_FAR}x${j} : unit ; "
    done
    last_i="$i"
    echo "Module Test$i."
    echo '  Goal True. idtac "Params: n=" '"$i"'. Abort.'
    echo '  Optimize Heap.'
    echo "  Time Record test := { ${FIELDS_SO_FAR} }."
    echo '  Optimize Heap.'
    echo '  Goal True.'
    echo '    restart_timer;'
    echo "    let v := constr:(forall v : test, x${i} v = x${i} v) in"
    echo '    finish_timing ( "Tactic call build" );'
    echo '    time "assert" assert v; [ intro x | shelve ];'
    echo '    time "destruct" destruct x;'
    echo '    time "cbn" cbn.'
    echo '  Abort.'
    echo "End Test$i."
    echo
done
