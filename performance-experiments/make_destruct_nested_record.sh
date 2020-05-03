#!/usr/bin/env bash
# USAGE: $0 SIZE

case "$1" in
    SuperFast)
        min=1
        max=450
        step=1
        ;;
    Fast)
        min=500
        max=1500
        step=100
        ;;
    Medium)
        min=1500
        max=2000
        step=100
        ;;
    Slow)
        min=2000
        max=2000
        step=100
        ;;
    VerySlow)
        min=2000
        max=2000
        step=100
        ;;
    * )
        echo "Invalid argument '$1'" >&2
        exit 1
esac

FIELDS_SO_FAR=""
for j in $(seq 1 $min); do
    FIELDS_SO_FAR="${FIELDS_SO_FAR}x${j} : unit ; "
done
echo 'Unset Boolean Equality Schemes.'
echo 'Unset Case Analysis Schemes.'
echo 'Unset Decidable Equality Schemes.'
echo 'Unset Elimination Schemes.'
echo 'Unset Primitive Projections.'
echo 'Unset Rewriting Schemes.'
echo 'Unset Nonrecursive Elimination Schemes.'
for i in $(seq $min $step $max); do
    echo "Module Test$i."
    echo '  Goal True. idtac "Params: n=" '"$i"'. Abort.'
    echo "  Time Record test := { ${FIELDS_SO_FAR} }."
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
    for j in $(seq $(($i+1)) $(($i+$step))); do
        FIELDS_SO_FAR="${FIELDS_SO_FAR}x${j} : unit ; "
    done
done
