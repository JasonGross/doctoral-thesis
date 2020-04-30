Require Import PerformanceExperiments.Harness.
Require Import PerformanceExperiments.make_nested_sig_common.

Definition args_of_size (s : size) : list nat
  := match s with
     | SuperFast => List.map (fun x => x * 100) (seq 0 120)
     | Fast => List.map (fun x => x * 100) (seq 0 151)
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac mkgoal n := constr:(Prim.goal2_sig n).
Ltac redgoal _ := once (time "cbv" (do_redgoal (); intros)).
Ltac time_solve_goal0 n := idtac.
Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.
(*
Goal True. run0 Fast.
*)
