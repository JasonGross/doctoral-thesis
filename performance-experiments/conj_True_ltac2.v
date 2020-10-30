Require Import Ltac2.Ltac2.
Require Import Ltac2.Constr.
Require Import Ltac2.Control.
Require Ltac2.Notations.
Require Ltac2.Array.
Require Ltac2.Int.
Require PerformanceExperiments.Ltac2Compat.Array.
Require Import PerformanceExperiments.Harness.
Require PerformanceExperiments.conj_True_uconstr.

Notation and_True := conj_True_uconstr.and_True.
Notation args_of_size := conj_True_uconstr.args_of_size.

Module Import WithLtac2.
  Import Ltac2.Notations.

  Ltac2 rec build_conj_true (n : int) (and : constr) (conj : constr) (tru : constr) (i : constr) :=
    match Int.lt 0 n with
    | false => (i, tru)
    | true
      => match build_conj_true (Int.sub n 1) and conj tru i with
         | (term, ty)
           => (Unsafe.make (Unsafe.App conj (Array.of_list [tru;ty;i;term])),
               Unsafe.make (Unsafe.App and (Array.of_list [tru;ty])))
         end
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
                  let v := Control.time (Some "build") (fun _ => match build_conj_true n' 'and '(@conj) 'True 'I with (term, ty) => term end) in
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
