Require Import Coq.Structures.Orders.
Require Import Coq.Bool.Bool.
Require Import Coq.Sorting.Mergesort.
Require Export Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Export ListNotations.

Global Set Printing Width 200.
Global Open Scope Z_scope.
Global Open Scope nat_scope.
Global Open Scope list_scope.

(** divisions should be roughly:
- All [SuperFast] tests in a file should finish in under 10 seconds total
- The [Fast] tests should take under 10 seconds each
- The [Medium] tests should go up to about a minute each
- The [Slow] tests should go up to about 10 minutes each
- The [VerySlow] tests may take longer than 10 minutes each *)

Inductive size := SuperFast | Fast | Medium | Slow | VerySlow.

Definition smaller_sizes (sz : size) : list size
  := match sz with
     | SuperFast => []
     | Fast => [SuperFast]
     | Medium => [SuperFast; Fast]
     | Slow => [SuperFast; Fast; Medium]
     | VerySlow => [SuperFast; Fast; Medium; Slow]
     end.

Fixpoint uniquify {T} (T_beq : T -> T -> bool) (ls : list T) : list T
  := match ls with
     | nil => nil
     | cons x xs
       => (if existsb (T_beq x) xs then (fun xs => xs) else cons x)
            (uniquify T_beq xs)
     end.

Definition remove_smaller_args_of_size {T} (T_beq : T -> T -> bool) (sz : size)
           (args_of_size : size -> list T)
  : list T
  := let args := uniquify T_beq (args_of_size sz) in
     let smaller_args := flat_map args_of_size (smaller_sizes sz) in
     filter (fun v => negb (existsb (T_beq v) smaller_args)) args.

Module NatProdOrder <: TotalLeBool.
  Definition t := (nat * nat)%type.
  Definition t_to_Z (v : t) : Z := (Z.of_nat (fst v) * Z.of_nat (snd v))%Z.
  Definition ltb (x y : t) : bool
    := (t_to_Z x <? t_to_Z y)%Z
       || (((t_to_Z x =? t_to_Z y)%Z)
             && ((fst x <? fst y)
                 || ((fst x =? fst y) && (snd x <? snd y)))).
  Definition leb (x y : t) : bool
    := ltb x y || ((fst x =? fst y) && (snd x =? snd y)).
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    cbv [leb ltb]; intros a1 a2.
    repeat first [ rewrite !Bool.andb_true_iff
                 | rewrite !Bool.orb_true_iff
                 | rewrite !Nat.eqb_eq
                 | rewrite !Z.eqb_eq
                 | rewrite !Z.ltb_lt
                 | rewrite !Nat.ltb_lt ].
    destruct (Z.lt_total (t_to_Z a1) (t_to_Z a2)) as [?|[?|?]];
      try solve [ auto ]; [].
    destruct (Nat.lt_total (fst a1) (fst a2)) as [?|[?|?]];
      try solve [ auto 6 ]; [].
    destruct (Nat.lt_total (snd a1) (snd a2)) as [?|[?|?]];
      solve [ auto 7 ].
  Qed.
End NatProdOrder.

Module NatProdSort := Sort NatProdOrder.
Notation sort_by_prod := NatProdSort.sort.

Module NatFstOrder <: TotalLeBool.
  Definition t := (nat * nat)%type.
  Definition ltb (x y : t) : bool
    := (fst x <? fst y)
       || ((fst x =? fst y)
             && (snd x <? snd y)).
  Definition leb (x y : t) : bool
    := ltb x y || ((fst x =? fst y) && (snd x =? snd y)).
  Theorem leb_total : forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    cbv [leb ltb]; intros a1 a2.
    repeat first [ rewrite !Bool.andb_true_iff
                 | rewrite !Bool.orb_true_iff
                 | rewrite !Nat.eqb_eq
                 | rewrite !Nat.ltb_lt ].
    destruct (Nat.lt_total (fst a1) (fst a2)) as [?|[?|?]];
      try solve [ auto 6 ]; [].
    destruct (Nat.lt_total (snd a1) (snd a2)) as [?|[?|?]];
      solve [ auto 7 ].
  Qed.
End NatFstOrder.

Module NatFstSort := Sort NatFstOrder.
Notation sort_by_fst := NatFstSort.sort.

Existing Class reflect.
Notation reflect_rel R1 R2 := (forall x y, reflect (R1 x y) (R2 x y)).

Lemma reflect_of_beq {beq : bool} {R : Prop}
      (bp : beq = true -> R)
      (pb : R -> beq = true)
  : reflect R beq.
Proof.
  destruct beq; constructor; intuition (discriminate || auto).
Qed.

Definition reflect_rel_of_beq {T} {beq : T -> T -> bool} {R : T -> T -> Prop}
      (bp : forall x y, beq x y = true -> R x y)
      (pb : forall x y, R x y -> beq x y = true)
  : reflect_rel R beq
  := fun x y => reflect_of_beq (bp x y) (pb x y).

Definition reflect_rel_of_beq_iff {T} {beq : T -> T -> bool} {R : T -> T -> Prop}
      (bp : forall x y, beq x y = true <-> R x y)
  : reflect_rel R beq
  := reflect_rel_of_beq (fun x y => proj1 (bp x y)) (fun x y => proj2 (bp x y)).

Instance reflect_eq_nat : reflect_rel (@eq nat) Nat.eqb
  := reflect_rel_of_beq_iff Nat.eqb_eq.

Definition remove_smaller_args_of_size_by_reflect
           {T} {T_beq : T -> T -> bool}
           {T_reflect : reflect_rel (@eq T) T_beq}
           (sz : size)
           (args_of_size : size -> list T)
  : list T
  := let args := uniquify T_beq (args_of_size sz) in
     let smaller_args := flat_map args_of_size (smaller_sizes sz) in
     filter (fun v => negb (existsb (T_beq v) smaller_args)) args.

Ltac runtests args_of_size describe_goal mkgoal redgoal time_solve_goal sz :=
  let args := (eval vm_compute in (remove_smaller_args_of_size_by_reflect sz args_of_size)) in
  let rec iter ls :=
      lazymatch ls with
      | [] => idtac
      | ?x :: ?xs
        => describe_goal x;
           let T := mkgoal x in
           try (solve [ assert T by (redgoal x; once (time_solve_goal x)) ]; []);
           iter xs
      end in
  iter args.

(*
Module LiftLetsMap.
  Import Examples.LiftLetsMap.
  Global Open Scope nat_scope.

  Definition args_of_size' (test_tac_n : nat) (s : size)
    := let '(n_count, m_count)
           := match test_tac_n, s with
              | 0, SuperFast => (10, 10)
              | 3, SuperFast => (50, 50)
              | 4, SuperFast => (50, 50)
              | _, SuperFast => (5, 4)
              | 0, Fast => (90, 90)
              | 3, Fast => (150, 150) (* N.B. test 3 stack overflows on larger than ~160, 160 *)
              | 4, Fast => (150, 150)
              | _, Fast => (6, 5)
              | 0, Medium => (115, 115) (* maybe should be (150, 150), but (115, 115) already takes over 11 h, I think *)
              | 5, Medium => (7, 8)
              | _, Medium => (6, 7)
              | 0, Slow => (200, 200) (* ??? *)
              | _, Slow => (10, 10) (* ??? *)
              | 0, VerySlow => (400, 400) (* ??? *)
              | _, VerySlow => (100, 100) (* ??? *)
              end in
       sort_by_prod (flat_map (fun n => map (fun m => (n, m)) (seq 1 m_count)) (seq 1 n_count)).
  Definition args_of_size (test_tac_n : nat) (s : size)
    := remove_smaller_args_of_size (Prod.prod_beq _ _ Nat.eqb Nat.eqb) s (args_of_size' test_tac_n).

  Ltac run test_tac_n size :=
    let test_for_tac := test_for_of_size size test_for_safe test_for in
    let args := (eval vm_compute in (args_of_size test_tac_n size)) in
    let test_tac := lazymatch test_tac_n with
                    | 0 => timetest0
                    | 1 => timetest1
                    | 2 => timetest2
                    | 3 => timetest3
                    | 4 => timetest4
                    | 5 => timetest5
                    end in
    let rec iter ls :=
        lazymatch ls with
        | [] => idtac
        | (?n, ?m) :: ?ls
          => test_for test_tac test_tac_n n m;
             iter ls
        end in
    iter args.
End LiftLetsMap.

Module Plus0Tree.
  Import Examples.Plus0Tree.
  Global Open Scope nat_scope.

  Definition args_of_size' (test_tac_n : nat) (s : size)
    := let ls
           := match test_tac_n, s with
              | 0, SuperFast => [(11, 2); (7, 4)]
              | 1, SuperFast => [(12, 3)]
              | 2, SuperFast => [(8, 3)]
              | 3, SuperFast => [(9, 3)]
              | 4, SuperFast => [(7, 3)]
              | 0, Fast => [(14, 5); (13, 20); (9, 1000)]
              | 1, Fast => [(14, 2); (13, 3); (9, 18); (5, 50); (4, 130); (3, 200); (2, 340); (1, 600)]
              | 2, Fast => [(10, 2); (9, 3); (8, 5); (7, 9); (6, 15); (5, 30); (4, 40); (3, 95); (2, 180); (1, 380)]
              | 3, Fast => [(10, 1); (9, 3); (8, 7); (7, 15); (6, 25); (5, 50); (4, 80); (3, 150); (2, 270); (1, 550)]
              | 4, Fast => [(9, 1); (8, 2); (7, 3); (6, 5); (5, 11); (4, 30); (3, 60); (2, 110); (1, 260)]
              | 0, Medium => [(16, 3); (12, 100)]
              | 1, Medium => [(15, 3); (9, 40)]
              | 2, Medium => [(11, 2); (10, 3); (9, 10)]
              | 3, Medium => [(11, 2); (10, 3); (9, 12)]
              | 4, Medium => [(9, 2); (8, 3); (10, 1)]
              | 0, Slow => [(16, 4)] (* ??? *)
              | 1, Slow => [(16, 4)] (* ??? *)
              | 2, Slow => [(12, 4)] (* ? (11, 3) is 122.176s *)
              | 3, Slow => [(12, 4)] (* ? (11, 3) is 165.575s *)
              | 4, Slow => [(9, 3); (10, 2); (11, 1)] (* ? should we have more for smaller fst of the pair? *)
              | _, VerySlow => [(1000, 1000)] (* ??? *)
              | _, _ => []
              end in
       sort_by_fst
         (flat_map
            (fun '(n_count, m_count)
             => flat_map (fun n => map (fun m => (n, m)) (seq 1 m_count)) (seq 1 n_count))
            ls).
  Definition args_of_size (test_tac_n : nat) (s : size)
    := remove_smaller_args_of_size (Prod.prod_beq _ _ Nat.eqb Nat.eqb) s (args_of_size' test_tac_n).

  Ltac run test_tac_n size :=
    let test_for_tac := test_for_of_size size test_for_safe test_for in
    let args := (eval vm_compute in (args_of_size test_tac_n size)) in
    let test_tac := lazymatch test_tac_n with
                    | 0 => timetest0
                    | 1 => timetest1
                    | 2 => timetest2
                    | 3 => timetest3
                    | 4 => timetest4
                    end in
    let rec iter ls :=
        lazymatch ls with
        | [] => idtac
        | (?n, ?m) :: ?ls
          => test_for test_tac n m;
             iter ls
        end in
    iter args.
End Plus0Tree.

Module SieveOfEratosthenes.
  Import Examples.SieveOfEratosthenes.
  Global Open Scope nat_scope.

  Definition args_of_size (test_tac_n : nat) (s : size)
    := match test_tac_n, s with
       | 0%nat, SuperFast => [(2, 3, 1); (5, 49, 2)]
       | 1%nat, SuperFast => [(2, 3, 1); (5, 1199, 2)]
       | 2%nat, SuperFast => [(2, 3, 1); (5, 449, 2)]
       | 3%nat, SuperFast => [(2, 3, 1); (5, 499, 2)]
       | 4%nat, SuperFast => [(2, 3, 1); (5, 39, 2)]
       | 5%nat, SuperFast => [(2, 3, 1); (5, 39, 2)]
       | 6%nat, SuperFast => [(2, 3, 1); (5, 39, 2)]
       | 0%nat, Fast => [(51, 4999, 2)]
       | 1%nat, Fast => [(1201, 4999, 2)]
       | 2%nat, Fast => [(451, 3999, 2)]
       | 3%nat, Fast => [(501, 4999, 2)]
       | 4%nat, Fast => [(41, 4999, 2)]
       | 5%nat, Fast => [(41, 79, 2)]
       | 6%nat, Fast => [(41, 79, 2)]
       | 2%nat, Medium => [(4001, 4999, 2)]
       | 5%nat, Medium => [(81, 149, 2)]
       | 6%nat, Medium => [(81, 149, 2)]
       | 5%nat, Slow => [(151, 189, 2)]
       | 6%nat, Slow => [(151, 189, 2)]
       | 5%nat, VerySlow => [(191, 4999, 2)]
       | 6%nat, VerySlow => [(191, 4999, 2)]
       | 0%nat, _ | 1%nat, _ | 2%nat, _ | 3%nat, _ | 4%nat, _ => []
       | _, _ => []
       end%Z.

  Ltac run test_tac_n size :=
    let test_from_to_tac := test_for_of_size size test_from_to_safe test_from_to in
    let args := (eval vm_compute in (args_of_size test_tac_n size)) in
    let test_tac := lazymatch test_tac_n with
                    | 0 => timetest0
                    | 1 => timetest1
                    | 2 => timetest2
                    | 3 => timetest3
                    | 4 => timetest4
                    | 5 => timetest5
                    | 6 => timetest6
                    end in
    let rec iter ls :=
        lazymatch ls with
        | [] => idtac
        | (?min, ?max, ?step) :: ?ls
          => test_from_to_tac test_tac min max step;
             iter ls
        end in
    iter args.
End SieveOfEratosthenes.

Module UnderLetsPlus0.
  Import Examples.UnderLetsPlus0.
  Global Open Scope nat_scope.

  Definition args_of_size (test_tac_n : nat) (s : size)
    := match test_tac_n, s with
       | 0, SuperFast => [(1, 70, 1)]
       | 1, SuperFast => [(1, 70, 1)]
       | 2, SuperFast => [(1, 30, 1)]
       | 3, SuperFast => [(1, 30, 1)]
       | 0, Fast => [(71, 5000, 1)]
       | 1, Fast => [(71, 200, 1)]
       | 2, Fast => [(31, 60, 1)]
       | 3, Fast => [(31, 60, 1)]
       | 1, Medium => [(201, 371, 1)]
       | 2, Medium => [(61, 90, 1)]
       | 3, Medium => [(61, 90, 1)]
       | 1, Slow => [(372, 1000, 1)] (* ??? *)
       | 2, Slow => [(91, 600, 1)] (* ??? *)
       | 3, Slow => [(91, 600, 1)] (* ??? *)
       | 1, VerySlow => [(1001, 5000, 1)]
       | 2, VerySlow => [(601, 5000, 1)]
       | 3, VerySlow => [(601, 5000, 1)]
       | 0, _ => []
       | _, _ => []
       end.

  Ltac run test_tac_n size :=
    let test_from_to_tac := test_for_of_size size test_from_to_safe test_from_to in
    let args := (eval vm_compute in (args_of_size test_tac_n size)) in
    let test_tac := lazymatch test_tac_n with
                    | 0 => timetest0
                    | 1 => timetest1
                    | 2 => timetest2
                    | 3 => timetest3
                    end in
    let rec iter ls :=
        lazymatch ls with
        | [] => idtac
        | (?min, ?max, ?step) :: ?ls
          => test_from_to_tac test_tac min max step;
             iter ls
        end in
    iter args.
End UnderLetsPlus0.
*)
