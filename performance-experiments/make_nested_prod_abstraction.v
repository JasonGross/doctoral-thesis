Require Import PerformanceExperiments.Harness.
Require Import PerformanceExperiments.make_nested_sig_abstraction_common.

Definition args_of_size (s : size) : list nat
  := match s with
     | Sanity => seq 0 3
     | SuperFast => seq 0 60
     | Fast => seq 0 100
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac mkgoal0 n := constr:(True).
Ltac redgoal0 _ := idtac.
Ltac time_solve_goal0 n := once time "everything" do_prod n.
Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal0 redgoal0 time_solve_goal0 sz.
(*
Goal True. run0 Fast.
*)
