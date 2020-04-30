Require Import PerformanceExperiments.Harness.
Require Import PerformanceExperiments.make_nested_sig_common.

Definition args_of_size (s : size) : list nat
  := match s with
     | SuperFast => seq 0 30
     | Fast => seq 0 65
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac mkgoal n := constr:(goal2 n).
Ltac redgoal _ := do_redgoal (); intros.
Ltac time_solve_goal0 n :=
  time "repeat-destruct" do_destruct ();
  time "cbn" do_cbn_goal ().
Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.
(*
Goal True. run0 Fast.
*)
