Require Import PerformanceExperiments.Harness.

Fixpoint and_True (n : nat)
  := match n with
     | 0 => True
     | S n => True /\ and_True n
     end.

Definition args_of_size (s : size) : list nat
  := match s with
     | SuperFast => seq 0 100
     | Fast => seq 100 200
                   ++ List.map (fun x => 200 + x * 2) (seq 0 50)
                   ++ List.map (fun x => 300 + x * 5) (seq 0 20)
                   ++ List.map (fun x => 400 + x * 10) (seq 0 10)
                   ++ List.map (fun x => 500 + x * 50) (seq 0 10)
                   ++ List.map (fun x => 1000 + x * 100) (seq 0 10)
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac mkgoal n := constr:(and_True n).
Ltac describe_goal n := idtac "Goal:" n.
Ltac redgoal _ := vm_compute.
Ltac time_solve_goal n := time "repeat-constructor" repeat constructor.

Goal True. runtests args_of_size describe_goal mkgoal redgoal time_solve_goal Fast.
