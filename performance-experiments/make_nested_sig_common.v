Local Set Primitive Projections.
Fixpoint ltuple (n : nat) :=
  match n with
  | 0 => unit
  | S n => ltuple n * unit
  end%type.
Fixpoint rtuple (n : nat) :=
  match n with
  | 0 => unit
  | S n => unit * rtuple n
  end%type.
Fixpoint mkfst (n : nat) : ltuple n -> unit :=
  match n with
  | 0 => fun x => x
  | S n => fun x => mkfst n (fst x)
  end.
Fixpoint mksnd (n : nat) : rtuple n -> unit :=
  match n with
  | 0 => fun x => x
  | S n => fun x => mksnd n (snd x)
  end.
Fixpoint ltuple_sig (n : nat) :=
  match n with
  | 0 => unit
  | S n => { _ : ltuple_sig n & unit }
  end%type.
Fixpoint rtuple_sig (n : nat) :=
  match n with
  | 0 => unit
  | S n => { _ : unit & rtuple_sig n }
  end%type.
Fixpoint mkfst_sig (n : nat) : ltuple_sig n -> unit :=
  match n with
  | 0 => fun x => x
  | S n => fun x => mkfst_sig n (projT1 x)
  end.
Fixpoint mksnd_sig (n : nat) : rtuple_sig n -> unit :=
  match n with
  | 0 => fun x => x
  | S n => fun x => mksnd_sig n (projT2 x)
  end.

Notation goal1 n := (forall y, mkfst n y = mkfst n y) (only parsing).
Notation goal2 n := (forall y, mksnd n y = mksnd n y) (only parsing).
Notation goal1_sig n := (forall y, mkfst_sig n y = mkfst_sig n y) (only parsing).
Notation goal2_sig n := (forall y, mksnd_sig n y = mksnd_sig n y) (only parsing).

Module Prim.
  Set Implicit Arguments.
  Record prod A B := pair { fst : A ; snd : B }.
  Record sigT {A} (P : A -> Type) := existT { projT1 : A ; projT2 : P projT1 }.
  Module Export Notations.
    Declare Scope prim_type_scope.
    Declare Scope prim_scope.
    Delimit Scope prim_type_scope with prim_type.
    Delimit Scope prim_scope with prim.
    Arguments prod (A B)%prim_type.
    Infix "*" := prod : prim_type_scope.
    Infix "*" := prod : prim_scope.
    Add Printing Let prod.
    Arguments pair {A B}%prim_type (_ _)%prim.
    Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : prim_scope.
    Arguments fst {A B}%prim_type _%prim.
    Arguments snd {A B}%prim_type _%prim.

    Add Printing Let sigT.
    Arguments existT {A}%prim_type P%prim_type (_ _)%prim.
    Arguments projT1 {A P}%prim_type _%prim.
    Arguments projT2 {A P}%prim_type _%prim.
    Arguments sigT {A}%prim_type P%prim_type.
    Notation "{ x & P }" := (sigT (fun x => P)) : prim_type_scope.
    Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) : prim_type_scope.
  End Notations.
  Fixpoint ltuple (n : nat) :=
    match n with
    | 0 => unit
    | S n => ltuple n * unit
    end%prim_type.
  Fixpoint rtuple (n : nat) :=
    match n with
    | 0 => unit
    | S n => unit * rtuple n
    end%prim_type.
  Fixpoint mkfst (n : nat) : ltuple n -> unit :=
    match n with
    | 0 => fun x => x
    | S n => fun x => mkfst n (fst x)
    end.
  Fixpoint mksnd (n : nat) : rtuple n -> unit :=
    match n with
    | 0 => fun x => x
    | S n => fun x => mksnd n (snd x)
    end.
  Fixpoint ltuple_sig (n : nat) :=
    match n with
    | 0 => unit
    | S n => { _ : ltuple_sig n & unit }
    end%prim_type.
  Fixpoint rtuple_sig (n : nat) :=
    match n with
    | 0 => unit
    | S n => { _ : unit & rtuple_sig n }
    end%prim_type.
  Fixpoint mkfst_sig (n : nat) : ltuple_sig n -> unit :=
    match n with
    | 0 => fun x => x
    | S n => fun x => mkfst_sig n (projT1 x)
    end.
  Fixpoint mksnd_sig (n : nat) : rtuple_sig n -> unit :=
    match n with
    | 0 => fun x => x
    | S n => fun x => mksnd_sig n (projT2 x)
    end.

  Notation goal1 n := (forall y, mkfst n y = mkfst n y) (only parsing).
  Notation goal2 n := (forall y, mksnd n y = mksnd n y) (only parsing).
  Notation goal1_sig n := (forall y, mkfst_sig n y = mkfst_sig n y) (only parsing).
  Notation goal2_sig n := (forall y, mksnd_sig n y = mksnd_sig n y) (only parsing).
End Prim.
Export Prim.Notations.

Ltac do_destruct_step :=
  match goal with
  | [ x : prod _ _ |- _ ] => destruct x
  | [ x : @sigT _ _ |- _ ] => destruct x
  | [ x : Prim.prod _ _ |- _ ] => destruct x
  | [ x : @Prim.sigT _ _ |- _ ] => destruct x
  end.
Ltac do_destruct _ := repeat do_destruct_step.

Ltac do_redgoal _ := cbv [ltuple rtuple ltuple_sig rtuple_sig Prim.ltuple Prim.rtuple Prim.ltuple_sig Prim.rtuple_sig mkfst mksnd mkfst_sig mksnd_sig Prim.mkfst Prim.mksnd Prim.mkfst_sig Prim.mksnd_sig].
Ltac do_cbn_goal _ := cbn [fst snd projT1 projT2 Prim.fst Prim.snd Prim.projT1 Prim.projT2].
