Require Import PerformanceExperiments.Harness.

Fixpoint and_True (n : nat)
  := match n with
     | 0 => True
     | S n => True /\ and_True n
     end.

Ltac build_conj_true_cps n k :=
  lazymatch n with
  | 0 => k uconstr:(I) uconstr:(True)
  | S ?n
    => build_conj_true_cps
         n
         ltac:(fun term ty => k uconstr:(@conj True ty I term) uconstr:(@and True ty))
  end.

Definition args_of_size (s : size) : list nat
  := match s with
     | SuperFast => seq 1 100
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

Ltac mkgoal n := constr:(and_True (pred n)).
Ltac redgoal _ := vm_compute.
Ltac time_solve_goal0 n :=
  let n' := (eval cbv in (pred n)) in
  time "build-and-refine"
       let eval_early := match goal with _ => restart_timer end in
       let term := build_conj_true_cps n' ltac:(fun term ty => term) in
       let eval_early := match goal with _ => finish_timing ( "Tactic call build" ) end in
       let eval_early := match goal with _ => restart_timer end in
       let term := constr:(term) in
       let eval_early := match goal with _ => finish_timing ( "Tactic call to_constr" ) end in
       let eval_early := match goal with _ => restart_timer end in
       let __ := type of term in
       let eval_early := match goal with _ => finish_timing ( "Tactic call type_of" ) end in
       time "refine" refine term.
Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.

(*
Goal True.
  run0 Fast.
  *)
