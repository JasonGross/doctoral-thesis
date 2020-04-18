Require Import PerformanceExperiments.Harness.

Definition args_of_size (s : size) : nat
  := match s with
     | SuperFast => 1500
     | Fast => 4000
     | Medium => 4000 + 4000
     | Slow => 0
     | VerySlow => 0
     end.

Ltac mkgoal_step _ := pose proof I.
Ltac time_solve_goal0 n tac :=
  time "uconstr-I-1000" (do 1000 let v := tac () in idtac).
Ltac run0 sz tac := Harness.runtests_step_arg args_of_size default_describe_goal mkgoal_step time_solve_goal0 sz tac.
(*
Goal True.
  let tac := ltac:(fun _ => uconstr:(I)) in
  run0 SuperFast tac.
*)
