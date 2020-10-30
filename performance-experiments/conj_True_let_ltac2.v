Require Import Ltac2.Ltac2.
Require Import Ltac2.Constr.
Require Import Ltac2.Control.
Require Ltac2.Notations.
Require Ltac2.Array.
Require Ltac2.Int.
Require PerformanceExperiments.Ltac2Compat.Array.
Require Import PerformanceExperiments.Ltac2Compat.Constr.
Require Import PerformanceExperiments.Harness.
Require PerformanceExperiments.conj_True_uconstr.

Notation and_True := conj_True_uconstr.and_True.
Notation args_of_size := conj_True_uconstr.args_of_size.

Module Import WithLtac2.
  Import Ltac2.Notations.

  Ltac2 rec mkres (n : int) (t : constr) (v : constr) (prop : constr) (and : constr) (conj : constr) (tru : constr) (i : constr) :=
    match Int.lt 0 n with
    | false => Unsafe.make
                 (Unsafe.mkLetIn
                    (Binder.make None t)
                    prop
                    v)
    | true
      => let rest := mkres (Int.sub n 1)
                           (Unsafe.make (Unsafe.App and (Array.of_list [tru;Unsafe.make (Unsafe.Rel 2)])))
                           (Unsafe.make (Unsafe.App conj (Array.of_list [tru;Unsafe.make (Unsafe.Rel 3);i;Unsafe.make (Unsafe.Rel 2)])))
                           prop and conj tru i in
         Unsafe.make
           (Unsafe.mkLetIn
              (Binder.make None t)
              prop
              (Unsafe.make
                 (Unsafe.mkLetIn
                    (Binder.make None v)
                    (Unsafe.make (Unsafe.Rel 1))
                    rest)))
    end.

  Ltac2 rec int_of_nat n :=
    (lazy_match! n with
    | 0 => 0
    | S ?n => Int.add 1 (int_of_nat n)
     end).
  Ltac2 time_solve_goal0 n :=
    let n := int_of_nat n in
    let n' := Int.sub n 1 in
    let v := Control.time
               (Some "build-and-typecheck")
               (fun _ =>
                  let v := Control.time (Some "build") (fun _ => mkres n' 'True 'I 'Prop 'and '(@conj) 'True 'I) in
                  let __ := Control.time (Some "typecheck") (fun _ => Unsafe.check v) in
                  v) in
    Control.time (Some "refine") (fun _ => refine v).
End WithLtac2.

Ltac mkgoal n := constr:(and_True (pred n)).
Ltac redgoal _ := vm_compute.
Ltac time_solve_goal0 :=
  ltac2:(n |- time_solve_goal0 (match (Ltac1.to_constr n) with Some v => v | None => 'I end)).
Ltac run0 sz := Harness.runtests args_of_size default_describe_goal mkgoal redgoal time_solve_goal0 sz.
Global Set Default Proof Mode "Classic".
(*
Goal True. run0 Fast.
*)
