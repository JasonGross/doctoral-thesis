#!/usr/bin/env bash
# USAGE: $0 SIZE

case "$1" in
    SuperFast)
        min=1
        max=1500
        ;;
    Fast)
        min=1500
        max=4000
        ;;
    Medium)
        min=4000
        max=8000
        ;;
    Slow)
        min=8000
        max=8000
        ;;
    VerySlow)
        min=8000
        max=8000
        ;;
    *)
        echo "Invalid argument '$1'" >&2
        exit 1
esac

SO_FAR=""
for j in $(seq 1 $(($min-1))); do
    SO_FAR="${SO_FAR}($(make_name "$j") : True) "
done
echo 'Goal True.'
for i in $(seq $min $max); do
    echo '  idtac "Params: n=" '"$i"';'
    echo '  restart_timer;'
    echo '  let v := uconstr:(fun'
    SO_FAR="${SO_FAR}($(make_name "$i") : True) "
    echo "  ${SO_FAR} => True) in"
    echo '  finish_timing ( "Tactic call uconstr-lambda" );'
    echo '  restart_timer;'
    echo '  let v := constr:(v) in'
    echo '  finish_timing ( "Tactic call to_constr" );'
    echo '  idtac.'
done
echo 'Abort.'
