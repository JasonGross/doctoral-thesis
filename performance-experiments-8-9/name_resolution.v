Require Import PerformanceExperiments.Harness.

Definition args_of_size (s : size) : list nat
  := match s with
     | SuperFast => seq 0 1500
     | Fast => seq 0 4000
     | Medium => seq 0 (4000 + 4000)
     | Slow => []
     | VerySlow => []
     end.

Ltac step_goal _ := pose proof I.
Ltac redgoal _ := idtac.
Ltac time_solve_goal0 n tac :=
  time "uconstr-I-1000" (do 1000 let v := tac () in idtac).
Ltac run0 sz tac := Harness.runtests_step_arg args_of_size default_describe_goal step_goal redgoal time_solve_goal0 sz tac.
(*
Goal True.
  let tac := ltac:(fun _ => uconstr:(I)) in
  run0 SuperFast tac.
*)
