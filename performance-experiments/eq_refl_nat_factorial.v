Require Import PerformanceExperiments.Harness.

Fixpoint fact (n : nat)
  := match n with
     | 0 => 1
     | S n' => n * fact n'
     end.

Global Strategy 1 [id].

Definition args_of_size (s : size) : list nat
  := match s with
     | SuperFast => seq 0 11
     | Fast => seq 0 12
     | Medium => []
     | Slow => []
     | VerySlow => []
     end.

Ltac mkgoal n := True.
Ltac redgoal _ := idtac.
Ltac time_solve_goal0 n :=
  time "constr-eq-refl" (idtac; let v := constr:(@eq_refl nat (fact n) : @id nat (fact n) = fact n) in idtac).
Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.
(*
Goal True. run0 SuperFast.
*)
