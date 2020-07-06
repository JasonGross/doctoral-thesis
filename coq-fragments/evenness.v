Require Import Coq.Arith.Arith.
Require Import Coq.NArith.NArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.

Definition Let_In {A B} (v : A) (f : A -> B) := let x := v in f x.
Notation "'dlet' x := v 'in' f" := (Let_In v (fun x => f)) (x ident, at level 200).

Inductive is_even : nat -> Prop :=
| even_O : is_even O
| even_SS : forall x, is_even x -> is_even (S (S x)).

Inductive expr {var : Type} :=
| NatO : expr
| NatS : expr -> expr
| NatMul : expr -> expr -> expr
| Var : var -> expr
| LetIn : expr -> (var -> expr) -> expr.
Notation "'elet' x := v 'in' f" := (LetIn v (fun x => f)) (x ident, at level 200).

Fixpoint denote (t : @expr nat) : nat
  := match t with
     | NatO => O
     | NatS x => S (denote x)
     | NatMul x y => denote x * denote y
     | Var v => v
     | LetIn v f => dlet x := denote v in denote (f x)
     end.

Fixpoint check_is_even_expr (t : @expr bool) : bool
  := match t with
     | NatO => true
     | NatS x => negb (check_is_even_expr x)
     | NatMul x y => orb (check_is_even_expr x) (check_is_even_expr y)
     | Var v_even => v_even
     | LetIn v f => let v_even := check_is_even_expr v in check_is_even_expr (f v_even)
     end.

Definition Expr := forall var, @expr var.

Inductive related {var1 var2 : Type} : list (var1 * var2) -> @expr var1 -> @expr var2 -> Prop :=
| RelatedNatO {Γ} : related Γ NatO NatO
| RelatedNatS {Γ e1 e2} : related Γ e1 e2 -> related Γ (NatS e1) (NatS e2)
| RelatedNatMul {Γ x1 x2 y1 y2} : related Γ x1 x2 -> related Γ y1 y2 -> related Γ (NatMul x1 y1) (NatMul x2 y2)
| RelatedVar {Γ v1 v2} : List.In (v1, v2) Γ -> related Γ (Var v1) (Var v2)
| RelatedLetIn {Γ e1 e2 f1 f2}
 : related Γ e1 e2 -> (forall v1 v2, related ((v1, v2) :: Γ) (f1 v1) (f2 v2)) -> related Γ (LetIn e1 f1) (LetIn e2 f2).

Definition Wf (e : Expr) := forall var1 var2, related nil (e var1) (e var2).

Theorem check_is_even_expr_sound (e : Expr) (H : Wf e)
  : check_is_even_expr (e bool) = true -> is_even (denote (e nat)).
Admitted.

Fixpoint is_related {var1 var2 : Type} (Γ : list (var1 * var2)) (e1 : @expr var1) (e2 : @expr var2) : Prop :=
  match e1, e2 with
  | NatO, NatO => True
  | NatS e1, NatS e2 => is_related Γ e1 e2
  | NatMul x1 y1, NatMul x2 y2 => is_related Γ x1 x2 /\ is_related Γ y1 y2
  | Var v1, Var v2 => List.In (v1, v2) Γ
  | LetIn e1 f1, LetIn e2 f2 => is_related Γ e1 e2 /\ forall v1 v2, is_related ((v1, v2) :: Γ) (f1 v1) (f2 v2)
  | _, _ => False
  end.

Fixpoint is_related_elim {var1 var2 : Type} (Γ : list (var1 * var2)) (e1 : @expr var1) (e2 : @expr var2) : Prop :=
  match e1, e2 with
  | NatO, NatO => True
  | NatS e1, NatS e2 => is_related_elim Γ e1 e2
  | NatMul x1 y1, NatMul x2 y2 => forall P : Prop,
      (is_related_elim Γ x1 x2 -> is_related_elim Γ y1 y2 -> P) -> P
  | Var v1, Var v2 => forall (P : Prop),
      (forall n, List.nth_error Γ (N.to_nat n) = Some (v1, v2) -> P) -> P
  | LetIn e1 f1, LetIn e2 f2 => forall P : Prop,
      (is_related_elim Γ e1 e2 -> (forall v1 v2, is_related_elim ((v1, v2) :: Γ) (f1 v1) (f2 v2)) -> P)
      -> P
  | _, _ => False
  end.

Lemma related_of_is_related_elim {var1 var2 Γ e1 e2}
  : @is_related_elim var1 var2 Γ e1 e2 -> related Γ e1 e2.
Proof.
  revert Γ e2; induction e1, e2; cbn [is_related_elim] in *;
    intro H'; try constructor; try apply H'; try now auto.
  { clear; intro n; revert n Γ.
    induction n using N.peano_ind; destruct Γ;
      rewrite ?N2Nat.inj_succ;
      cbn [List.In nth_error N.to_nat];
      try solve [ intuition congruence ];
      eauto. }
Qed.

Ltac find ls v :=
  lazymatch ls with
  | cons v _ => constr:(O)
  | cons _ ?ls
    => let n := find ls v in
       constr:(S n)
  end.
Ltac solve_is_related_elim :=
  lazymatch goal with
  | [ |- is_related_elim _ _ _ ] => lazy -[List.nth_error N.to_nat]
  end;
  repeat lazymatch goal with
         | [ |- True ] => exact I
         | [ |- forall P, (?A -> ?B -> P) -> P ]
           => let P := fresh in
              let H := fresh in
              intros P H; apply H; clear P H
         | [ |- forall P, (forall n, List.nth_error ?Γ (N.to_nat n) = Some ?v -> P) -> P ]
           => let P := fresh in
              let H := fresh in
              let n := find Γ v in
              let n := (eval cbv in (N.of_nat n)) in
              intros P H; apply (H n); vm_compute; reflexivity
         | [ |- forall v1 v2, _ ] => intros ? ?
         end.

Ltac solve_related :=
  apply related_of_is_related_elim; solve_is_related_elim.

Ltac reify var Γ e :=
  let recr e := reify var Γ e in
  lazymatch e with
  | O => uconstr:(@NatO var)
  | S ?e => let e' := recr e in
            uconstr:(@NatS var e')
  | Nat.mul ?x ?y
    => let x' := recr x in
       let y' := recr y in
       uconstr:(@NatMul var x' y')
  | (let x := ?v in ?f)
    => recr (dlet x := v in f)
  | (dlet x := ?v in ?f)
    => let f' := fresh in
       let Γ' := fresh in
       let v' := fresh in
       let T := type of v in
       let ve := recr v in
       let fe := lazymatch
             constr:(
               fun (x : T) (v' : var)
               => match f, (x, v') :: Γ return _ with
                  | f', Γ'
                    => ltac:(let f := (eval cbv delta [f'] in f') in
                             let Γ := (eval cbv delta [Γ'] in Γ') in
                             let val := reify var Γ f in
                             refine val)
                  end) with
           | fun _ => ?f => f
           | ?e => fail 0 "Cannot eliminate functional dependencies of" e
           end in
       uconstr:(@LetIn var ve fe)
  | ?v
    => lazymatch Γ with
       | context[(v, ?v') :: _]
         => uconstr:(@Var var v')
       | _ => fail 0 "Cannot reify" v
       end
  end.
Ltac Reify e :=
  constr:(fun var : Type
          => ltac:(let r := reify var uconstr:(@nil _) e in
                   refine r)).

Strategy -10 [denote].
Strategy 10 [Let_In].

Goal is_even (dlet x := 100 * 100 * 100 * 100 in
              dlet y := x * x * x * x in
              y * y * y * y).
  lazymatch goal with
  | [ |- is_even ?v ]
    => let r := Reify v in
       let e := fresh "e" in
       pose r as e;
       change (is_even (denote (e nat)))
  end.
  apply check_is_even_expr_sound.
  { intros var1 var2; solve_related. }
  { vm_compute; reflexivity. }
Qed.
