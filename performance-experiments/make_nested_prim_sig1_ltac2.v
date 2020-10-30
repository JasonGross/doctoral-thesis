Require Import PerformanceExperiments.Harness.
Require Import PerformanceExperiments.make_nested_sig_common_ltac2.

Definition args_of_size (s : size) : list nat
  := match s with
     | Sanity => seq 0 3
     | SuperFast => seq 0 22
     | Fast => seq 0 23
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac mkgoal0 _ := constr:(Prop).
Ltac redgoal0 _ := idtac.
Ltac time_solve_goal0 n := once (WithLtac2.Prim.time_solve_goal_sig_1 n).
Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal0 redgoal0 time_solve_goal0 sz.
(*
Goal True. run0 Fast.
*)
