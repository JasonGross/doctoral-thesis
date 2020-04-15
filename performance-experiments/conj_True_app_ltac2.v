Require Import Ltac2.Ltac2.
Require Import Ltac2.Constr.
Require Import Ltac2.Control.
Require Ltac2.Notations.
Require Ltac2.Array.
Require Ltac2.Int.
Require Import PerformanceExperiments.Harness.
Require PerformanceExperiments.conj_True_let_ltac2.

Notation and_True := conj_True_let_ltac2.and_True.
Notation args_of_size := conj_True_let_ltac2.args_of_size.

Module Import WithLtac2.
  Import Ltac2.Notations.

  Module Array.
    (** modified from https://github.com/coq/coq/blob/227520b14e978e19d58368de873521a283aecedd/user-contrib/Ltac2/Array.v#L161-L182 *)
    Ltac2 rec of_list_aux (ls : 'a list) (dst : 'a array) (pos : int) :=
      match ls with
      | [] => ()
      | hd::tl =>
        Array.set dst pos hd;
  of_list_aux tl dst (Int.add pos 1)
    end.

    Ltac2 of_list (ls : 'a list) :=
      let rec list_length (ls : 'a list) :=
          match ls with
          | [] => 0
          | _ :: tl => Int.add 1 (list_length tl)
          end in
      match ls with
      | [] => Array.make 0 'I
      | hd::tl =>
        let anew := Array.make (list_length ls) hd in
        of_list_aux ls anew 0;
  anew
    end.
  End Array.

  Ltac2 rec mkres (n : int) (t : constr) (v : constr) (prop : constr) (and : constr) (conj : constr) (tru : constr) (i : constr) :=
    match Int.lt 0 n with
    | false => v
    | true
      => let rest := mkres (Int.sub n 1)
                           (Unsafe.make (Unsafe.App and (Array.of_list [tru;Unsafe.make (Unsafe.Rel 2)])))
                           (Unsafe.make (Unsafe.App conj (Array.of_list [tru;Unsafe.make (Unsafe.Rel 2);i;Unsafe.make (Unsafe.Rel 1)])))
                           prop and conj tru i in
         Unsafe.make
           (Unsafe.App
              (Unsafe.make
                 (Unsafe.Lambda
                    { binder_name := None ; binder_relevance := Relevant }
                    prop
                    (Unsafe.make
                       (Unsafe.Lambda
                          { binder_name := None ; binder_relevance := Relevant }
                          (Unsafe.make (Unsafe.Rel 1))
                          rest))))
              (Array.of_list [t; v]))
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
(*
Goal True. run0 Fast.
*)
