Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.

Set Primitive Projections.
Set Implicit Arguments.
Set Universe Polymorphism.

Obligation Tactic := cbv beta; trivial.

Record prod (A B:Type) : Type := pair { fst : A ; snd : B }.
Infix "*" := prod : type_scope.
Add Printing Let prod.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Arguments pair {A B} _ _.
Arguments fst {A B} _.
Arguments snd {A B} _.

Reserved Notation "g '∘' f" (at level 40, left associativity).
Reserved Notation "F '₀' x" (at level 10, no associativity, format "F '₀'  x").
Reserved Notation "F '₁' m" (at level 10, no associativity, format "F '₁'  m").
Reserved Infix "≅" (at level 70, no associativity).
Reserved Notation "x ≅ y :>>> T" (at level 70, no associativity).

Record Category :=
  {
    object :> Type;
    morphism : object -> object -> Type;

    identity : forall x, morphism x x;
    compose : forall s d d',
        morphism d d'
        -> morphism s d
        -> morphism s d'
    where "f '∘' g" := (compose f g);

    associativity : forall x1 x2 x3 x4
                           (m1 : morphism x1 x2)
                           (m2 : morphism x2 x3)
                           (m3 : morphism x3 x4),
        (m3 ∘ m2) ∘ m1 = m3 ∘ (m2 ∘ m1);

    left_identity : forall a b (f : morphism a b), identity b ∘ f = f;
    right_identity : forall a b (f : morphism a b), f ∘ identity a = f;

  }.

Declare Scope category_scope.
Declare Scope object_scope.
Declare Scope morphism_scope.
Bind Scope category_scope with Category.
Bind Scope object_scope with object.
Bind Scope morphism_scope with morphism.
Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope object_scope with object.

Arguments identity {_} _.
Arguments compose {_ _ _ _} _ _.

Infix "∘" := compose : morphism_scope.
Notation "1" := (identity _) : morphism_scope.
Local Open Scope morphism_scope.

Record isomorphic {C : Category} (s d : C) :=
  {
    fwd : morphism C s d
    ; bwd : morphism C d s
    ; iso1 : fwd ∘ bwd = 1
    ; iso2 : bwd ∘ fwd = 1
  }.

Notation "s ≅ d :>>> C" := (@isomorphic C s d) : morphism_scope.
Infix "≅" := isomorphic : morphism_scope.

Declare Scope functor_scope.
Delimit Scope functor_scope with functor.

Local Open Scope morphism_scope.

Record Functor (C D : Category) :=
  {
    object_of :> C -> D;
    morphism_of : forall s d, morphism C s d
                              -> morphism D (object_of s) (object_of d);
    composition_of : forall s d d'
                            (m1 : morphism C s d) (m2: morphism C d d'),
        morphism_of _ _ (m2 ∘ m1)
        = (morphism_of _ _ m2) ∘ (morphism_of _ _ m1);
    identity_of : forall x, morphism_of _ _ (identity x)
                            = identity (object_of x)
  }.

Arguments object_of {C D} _.
Arguments morphism_of {C D} _ {s d}.

Bind Scope functor_scope with Functor.

Notation "F '₀' x" := (object_of F x) : object_scope.
Notation "F '₁' m" := (morphism_of F m) : morphism_scope.

Declare Scope natural_transformation_scope.
Delimit Scope natural_transformation_scope with natural_transformation.

Module Functor.
  Program Definition identity (C : Category) : Functor C C
    := {| object_of x := x
          ; morphism_of s d m := m |}.

  Program Definition compose (s d d' : Category)
          (F1 : Functor d d') (F2 : Functor s d)
    : Functor s d'
    := {| object_of x := F1 (F2 x)
          ; morphism_of s d m := F1 ₁ (F2 ₁ m) |}.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
End Functor.

Infix "∘" := Functor.compose : functor_scope.
Notation "1" := (Functor.identity _) : functor_scope.

Local Open Scope morphism_scope.
Local Open Scope natural_transformation_scope.

Record NaturalTransformation {C D : Category} (F G : Functor C D) :=
  {
    components_of :> forall c, morphism D (F c) (G c);
    commutes : forall s d (m : morphism C s d),
        components_of d ∘ F ₁ m = G ₁ m ∘ components_of s
  }.

Bind Scope natural_transformation_scope with NaturalTransformation.

Module NaturalTransformation.
  Program Definition identity {C D : Category} (F : Functor C D) : NaturalTransformation F F
    := {| components_of x := 1 |}.
  Next Obligation. Admitted.

  Program Definition compose {C D : Category} (s d d' : Functor C D)
          (T1 : NaturalTransformation d d') (T2 : NaturalTransformation s d)
    : NaturalTransformation s d'
    := {| components_of x := T1 x ∘ T2 x |}.
  Next Obligation. Admitted.
End NaturalTransformation.

Infix "∘" := NaturalTransformation.compose : natural_transformation_scope.
Notation "1" := (NaturalTransformation.identity _) : natural_transformation_scope.

Program Definition functor_category (C D : Category) : Category
  := {| object := Functor C D
        ; morphism := @NaturalTransformation C D
        ; identity x := 1
        ; compose s d d' m1 m2 := m1 ∘ m2 |}%natural_transformation.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Notation "C -> D" := (functor_category C D) : category_scope.

Program Definition prod_category (C D : Category) : Category
  := {| object := C * D
        ; morphism s d := morphism C (fst s) (fst d) * morphism D (snd s) (snd d)
        ; identity x := (1, 1)
        ; compose s d d' m1 m2 := (fst m1 ∘ fst m2, snd m1 ∘ snd m2) |}%type%morphism.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Infix "*" := prod_category : category_scope.

Program Definition Cat : Category :=
  {|
    object := Category
    ; morphism := Functor
    ; compose s d d' m1 m2 := m1 ∘ m2
    ; identity x := 1
  |}%functor.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Local Open Scope object_scope.
Local Open Scope morphism_scope.
Local Open Scope category_scope.

Arguments Build_Functor _ _ & .
Arguments Build_isomorphic _ _ _ & .
Arguments Build_NaturalTransformation _ _ _ _ & .
Arguments pair _ _ & .
Canonical Structure default_eta {A B} (v : A * B) : A * B := (fst v, snd v).
Canonical Structure pair' {A B} (a : A) (b : B) : A * B := pair a b.

(** [(C₁ × C₂ → D) ≅ (C₁ → (C₂ → D))] *)
Time Program Definition curry_iso (C₁ C₂ D : Category)
  : (C₁ * C₂ -> D) ≅ (C₁ -> (C₂ -> D)) :>>> Cat
  := {| fwd
        := {| object_of F
              := {| object_of c₁
                    := {| object_of c₂ := F ₀ (c₁, c₂);
                          morphism_of s d m := F ₁ (identity c₁, m) |};
                    morphism_of s d m₁
                    := {| components_of c₂ := F ₁ (m₁, identity c₂) |} |};
              morphism_of s d T
              := {| components_of c₁
                    := {| components_of c₂ := T (c₁, c₂) |} |} |};
        bwd
        := {| object_of F
              := {| object_of '(c₁, c₂) := (F ₀ c₁)₀ c₂;
                    morphism_of '(s₁, s₂) '(d₁, d₂) '(m₁, m₂)
                    := (F ₁ m₁) d₂ ∘ (F ₀ s₁)₁ m₂ |};
              morphism_of s d T
              := {| components_of '(c₁, c₂) := (T c₁) c₂ |} |}; |}.
(* Finished transaction in 1.958 secs (1.958u,0.s) (successful) *)
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation.
(**
1 subgoal (ID 752)

  ============================
  forall C₁ C₂ D : Category,
  {|
  object_of := fun F : (C₁ -> C₂ -> D)%category =>
               {|
               object_of := fun pat : (C₁ * C₂)%category =>
                            (F₀ (fst pat))₀ (snd pat);
               morphism_of := fun (pat pat0 : (C₁ * C₂)%category)
                                (pat1 : morphism (C₁ * C₂)
                                          (fst pat, snd pat)
                                          (fst pat0, snd pat0)) =>
                              (F₁ (fst pat1)) (snd pat0)
                              ∘ (F₀ (fst pat))₁ (snd pat1);
               composition_of := curry_iso_obligation_7 F;
               identity_of := curry_iso_obligation_8 F |};
  morphism_of := fun (s d : (C₁ -> C₂ -> D)%category)
                   (T : morphism (C₁ -> C₂ -> D) s d) =>
                 {|
                 components_of := fun pat : (C₁ * C₂)%category =>
                                  T (fst pat) (snd pat);
                 commutes := curry_iso_obligation_9 T |};
  composition_of := curry_iso_obligation_11 (D:=D);
  identity_of := curry_iso_obligation_10 (D:=D) |}
  ∘ {|
    object_of := fun F : (C₁ * C₂ -> D)%category =>
                 {|
                 object_of := fun c₁ : C₁ =>
                              {|
                              object_of := fun c₂ : C₂ => F₀ (c₁, c₂);
                              morphism_of := fun (s d : C₂) (m : morphism C₂ s d)
                                             => F₁ (1, m);
                              composition_of := curry_iso_obligation_1 F c₁;
                              identity_of := curry_iso_obligation_2 F c₁ |};
                 morphism_of := fun (s d : C₁) (m₁ : morphism C₁ s d) =>
                                {|
                                components_of := fun c₂ : C₂ => F₁ (m₁, 1);
                                commutes := curry_iso_obligation_3 F s d m₁ |};
                 composition_of := curry_iso_obligation_5 F;
                 identity_of := curry_iso_obligation_4 F |};
    morphism_of := fun (s d : (C₁ * C₂ -> D)%category)
                     (T : morphism (C₁ * C₂ -> D) s d) =>
                   {|
                   components_of := fun c₁ : C₁ =>
                                    {|
                                    components_of := fun c₂ : C₂ => T (c₁, c₂);
                                    commutes := curry_iso_obligation_6 T c₁ |};
                   commutes := curry_iso_obligation_12 T |};
    composition_of := curry_iso_obligation_14 (D:=D);
    identity_of := curry_iso_obligation_13 (D:=D) |} = 1
 *)
  (** About 48 lines *)
  cbv [compose Cat Functor.compose NaturalTransformation.compose].
  (**
1 subgoal (ID 757)

  ============================
  forall C₁ C₂ D : Category,
  {|
  object_of := fun x : (C₁ * C₂ -> D)%category =>
               {|
               object_of := fun F : (C₁ -> C₂ -> D)%category =>
                            {|
                            object_of := fun pat : (C₁ * C₂)%category =>
                                         (F₀ (fst pat))₀
                                         (snd pat);
                            morphism_of := fun (pat pat0 : (C₁ * C₂)%category)
                                             (pat1 : morphism
                                                     (C₁ * C₂)
                                                     (fst pat, snd pat)
                                                     (fst pat0, snd pat0)) =>
                                           (F₁ (fst pat1)) (snd pat0)
                                           ∘ (F₀ (fst pat))₁
                                           (snd pat1);
                            composition_of := curry_iso_obligation_7 F;
                            identity_of := curry_iso_obligation_8 F |};
               morphism_of := fun (s d : (C₁ -> C₂ -> D)%category)
                                (T : morphism (C₁ -> C₂ -> D) s d) =>
                              {|
                              components_of := fun pat : (C₁ * C₂)%category =>
                                               T (fst pat) (snd pat);
                              commutes := curry_iso_obligation_9 T |};
               composition_of := curry_iso_obligation_11 (D:=D);
               identity_of := curry_iso_obligation_10 (D:=D) |}₀
               ({|
                object_of := fun F : (C₁ * C₂ -> D)%category =>
                             {|
                             object_of := fun c₁ : C₁ =>
                                          {|
                                          object_of := fun c₂ : C₂ => F₀ (c₁, c₂);
                                          morphism_of := fun
                                                     (s d : C₂)
                                                     (m : morphism C₂ s d) =>
                                                     F₁ (1, m);
                                          composition_of := curry_iso_obligation_1
                                                     F c₁;
                                          identity_of := curry_iso_obligation_2 F
                                                     c₁ |};
                             morphism_of := fun (s d : C₁) (m₁ : morphism C₁ s d)
                                            =>
                                            {|
                                            components_of := fun c₂ : C₂ =>
                                                     F₁ (m₁, 1);
                                            commutes := curry_iso_obligation_3 F s
                                                     d m₁ |};
                             composition_of := curry_iso_obligation_5 F;
                             identity_of := curry_iso_obligation_4 F |};
                morphism_of := fun (s d : (C₁ * C₂ -> D)%category)
                                 (T : morphism (C₁ * C₂ -> D) s d) =>
                               {|
                               components_of := fun c₁ : C₁ =>
                                                {|
                                                components_of := fun c₂ : C₂ =>
                                                     T (c₁, c₂);
                                                commutes := curry_iso_obligation_6
                                                     T c₁ |};
                               commutes := curry_iso_obligation_12 T |};
                composition_of := curry_iso_obligation_14 (D:=D);
                identity_of := curry_iso_obligation_13 (D:=D) |}₀ x);
  morphism_of := fun (s d : (C₁ * C₂ -> D)%category)
                   (m : morphism (C₁ * C₂ -> D) s d) =>
                 {|
                 object_of := fun F : (C₁ -> C₂ -> D)%category =>
                              {|
                              object_of := fun pat : (C₁ * C₂)%category =>
                                           (F₀ (fst pat))₀
                                           (snd pat);
                              morphism_of := fun (pat pat0 : (C₁ * C₂)%category)
                                               (pat1 :
                                                morphism
                                                  (C₁ * C₂)
                                                  (fst pat, snd pat)
                                                  (fst pat0, snd pat0)) =>
                                             (F₁ (fst pat1)) (snd pat0)
                                             ∘ (F₀ (fst pat))₁
                                             (snd pat1);
                              composition_of := curry_iso_obligation_7 F;
                              identity_of := curry_iso_obligation_8 F |};
                 morphism_of := fun (s0 d0 : (C₁ -> C₂ -> D)%category)
                                  (T : morphism (C₁ -> C₂ -> D) s0 d0) =>
                                {|
                                components_of := fun pat : (C₁ * C₂)%category =>
                                                 T (fst pat) (snd pat);
                                commutes := curry_iso_obligation_9 T |};
                 composition_of := curry_iso_obligation_11 (D:=D);
                 identity_of := curry_iso_obligation_10 (D:=D) |}₁
                 ({|
                  object_of := fun F : (C₁ * C₂ -> D)%category =>
                               {|
                               object_of := fun c₁ : C₁ =>
                                            {|
                                            object_of := fun c₂ : C₂ =>
                                                     F₀ (c₁, c₂);
                                            morphism_of := fun
                                                     (s0 d0 : C₂)
                                                     (m0 : morphism C₂ s0 d0) =>
                                                     F₁ (1, m0);
                                            composition_of := curry_iso_obligation_1
                                                     F c₁;
                                            identity_of := curry_iso_obligation_2
                                                     F c₁ |};
                               morphism_of := fun (s0 d0 : C₁)
                                                (m₁ : morphism C₁ s0 d0) =>
                                              {|
                                              components_of := fun c₂ : C₂ =>
                                                     F₁ (m₁, 1);
                                              commutes := curry_iso_obligation_3 F
                                                     s0 d0 m₁ |};
                               composition_of := curry_iso_obligation_5 F;
                               identity_of := curry_iso_obligation_4 F |};
                  morphism_of := fun (s0 d0 : (C₁ * C₂ -> D)%category)
                                   (T : morphism (C₁ * C₂ -> D) s0 d0) =>
                                 {|
                                 components_of := fun c₁ : C₁ =>
                                                  {|
                                                  components_of := fun c₂ : C₂ =>
                                                     T (c₁, c₂);
                                                  commutes := curry_iso_obligation_6
                                                     T c₁ |};
                                 commutes := curry_iso_obligation_12 T |};
                  composition_of := curry_iso_obligation_14 (D:=D);
                  identity_of := curry_iso_obligation_13 (D:=D) |}₁ m);
  composition_of := Functor.compose_obligation_1
                      {|
                      object_of := fun F : (C₁ -> C₂ -> D)%category =>
                                   {|
                                   object_of := fun pat : (C₁ * C₂)%category =>
                                                (F₀ (fst pat))₀
                                                (snd pat);
                                   morphism_of := fun
                                                    (pat
                                                     pat0 :
                                                     (C₁ * C₂)%category)
                                                    (pat1 :
                                                     morphism
                                                     (C₁ * C₂)
                                                     (fst pat, snd pat)
                                                     (fst pat0, snd pat0)) =>
                                                  (F₁ (fst pat1)) (snd pat0)
                                                  ∘ (F₀ (fst pat))₁
                                                  (snd pat1);
                                   composition_of := curry_iso_obligation_7 F;
                                   identity_of := curry_iso_obligation_8 F |};
                      morphism_of := fun (s d : (C₁ -> C₂ -> D)%category)
                                       (T : morphism (C₁ -> C₂ -> D) s d) =>
                                     {|
                                     components_of := fun pat : (C₁ * C₂)%category
                                                     =>
                                                     T (fst pat) (snd pat);
                                     commutes := curry_iso_obligation_9 T |};
                      composition_of := curry_iso_obligation_11 (D:=D);
                      identity_of := curry_iso_obligation_10 (D:=D) |}
                      {|
                      object_of := fun F : (C₁ * C₂ -> D)%category =>
                                   {|
                                   object_of := fun c₁ : C₁ =>
                                                {|
                                                object_of := fun c₂ : C₂ =>
                                                     F₀ (c₁, c₂);
                                                morphism_of := fun
                                                     (s d : C₂)
                                                     (m : morphism C₂ s d) =>
                                                     F₁ (1, m);
                                                composition_of := curry_iso_obligation_1
                                                     F c₁;
                                                identity_of := curry_iso_obligation_2
                                                     F c₁ |};
                                   morphism_of := fun
                                                    (s d : C₁)
                                                    (m₁ : morphism C₁ s d) =>
                                                  {|
                                                  components_of := fun c₂ : C₂ =>
                                                     F₁ (m₁, 1);
                                                  commutes := curry_iso_obligation_3
                                                     F s d m₁ |};
                                   composition_of := curry_iso_obligation_5 F;
                                   identity_of := curry_iso_obligation_4 F |};
                      morphism_of := fun (s d : (C₁ * C₂ -> D)%category)
                                       (T : morphism (C₁ * C₂ -> D) s d) =>
                                     {|
                                     components_of := fun c₁ : C₁ =>
                                                     {|
                                                     components_of := fun c₂ : C₂
                                                     => T (c₁, c₂);
                                                     commutes := curry_iso_obligation_6
                                                     T c₁ |};
                                     commutes := curry_iso_obligation_12 T |};
                      composition_of := curry_iso_obligation_14 (D:=D);
                      identity_of := curry_iso_obligation_13 (D:=D) |};
  identity_of := Functor.compose_obligation_2
                   {|
                   object_of := fun F : (C₁ -> C₂ -> D)%category =>
                                {|
                                object_of := fun pat : (C₁ * C₂)%category =>
                                             (F₀ (fst pat))₀
                                             (snd pat);
                                morphism_of := fun (pat pat0 : (C₁ * C₂)%category)
                                                 (pat1 :
                                                  morphism
                                                    (C₁ * C₂)
                                                    (fst pat, snd pat)
                                                    (fst pat0, snd pat0)) =>
                                               (F₁ (fst pat1)) (snd pat0)
                                               ∘ (F₀ (fst pat))₁
                                               (snd pat1);
                                composition_of := curry_iso_obligation_7 F;
                                identity_of := curry_iso_obligation_8 F |};
                   morphism_of := fun (s d : (C₁ -> C₂ -> D)%category)
                                    (T : morphism (C₁ -> C₂ -> D) s d) =>
                                  {|
                                  components_of := fun pat : (C₁ * C₂)%category =>
                                                   T (fst pat) (snd pat);
                                  commutes := curry_iso_obligation_9 T |};
                   composition_of := curry_iso_obligation_11 (D:=D);
                   identity_of := curry_iso_obligation_10 (D:=D) |}
                   {|
                   object_of := fun F : (C₁ * C₂ -> D)%category =>
                                {|
                                object_of := fun c₁ : C₁ =>
                                             {|
                                             object_of := fun c₂ : C₂ =>
                                                     F₀ (c₁, c₂);
                                             morphism_of := fun
                                                     (s d : C₂)
                                                     (m : morphism C₂ s d) =>
                                                     F₁ (1, m);
                                             composition_of := curry_iso_obligation_1
                                                     F c₁;
                                             identity_of := curry_iso_obligation_2
                                                     F c₁ |};
                                morphism_of := fun (s d : C₁)
                                                 (m₁ : morphism C₁ s d) =>
                                               {|
                                               components_of := fun c₂ : C₂ =>
                                                     F₁ (m₁, 1);
                                               commutes := curry_iso_obligation_3
                                                     F s d m₁ |};
                                composition_of := curry_iso_obligation_5 F;
                                identity_of := curry_iso_obligation_4 F |};
                   morphism_of := fun (s d : (C₁ * C₂ -> D)%category)
                                    (T : morphism (C₁ * C₂ -> D) s d) =>
                                  {|
                                  components_of := fun c₁ : C₁ =>
                                                   {|
                                                   components_of := fun c₂ : C₂ =>
                                                     T (c₁, c₂);
                                                   commutes := curry_iso_obligation_6
                                                     T c₁ |};
                                  commutes := curry_iso_obligation_12 T |};
                   composition_of := curry_iso_obligation_14 (D:=D);
                   identity_of := curry_iso_obligation_13 (D:=D) |} |} = 1
   *)
  (** About 254 lines *)
Admitted.
Next Obligation. Admitted.
