Require Import Coq.Program.Basics.
Require Import Coq.Program.Tactics.

Set Primitive Projections.
Set Implicit Arguments.
Set Universe Polymorphism.
Set Printing Width 50.

Obligation Tactic := cbv beta; trivial.

Record prod (A B:Type) : Type := pair { fst : A ; snd : B }.
Infix "*" := prod : type_scope.
Add Printing Let prod.
Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
Arguments pair {A B} _ _.
Arguments fst {A B} _.
Arguments snd {A B} _.

Reserved Notation "g '∘' f" (at level 40, left associativity).
Reserved Notation "F '₀' x"
         (at level 10, no associativity, format "'[' F '₀' ']'  x").
Reserved Notation "F '₁' m"
         (at level 10, no associativity, format "'[' F '₁' ']'  m").
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
  Program Definition identity {C D : Category} (F : Functor C D)
  : NaturalTransformation F F
    := {| components_of x := 1 |}.
  Next Obligation. Admitted.

  Program Definition compose {C D : Category} (s d d' : Functor C D)
          (T1 : NaturalTransformation d d') (T2 : NaturalTransformation s d)
    : NaturalTransformation s d'
    := {| components_of x := T1 x ∘ T2 x |}.
  Next Obligation. Admitted.
End NaturalTransformation.

Infix "∘" := NaturalTransformation.compose
             : natural_transformation_scope.
Notation "1" := (NaturalTransformation.identity _)
                : natural_transformation_scope.

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
        ; morphism s d
          := morphism C (fst s) (fst d) * morphism D (snd s) (snd d)
        ; identity x := (1, 1)
        ; compose s d d' m1 m2 := (fst m1 ∘ fst m2, snd m1 ∘ snd m2)
     |}%type%morphism.
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

Local Open Scope functor_scope.
Local Open Scope natural_transformation_scope.
Local Open Scope object_scope.
Local Open Scope morphism_scope.
Local Open Scope category_scope.

Arguments Build_Functor _ _ & .
Arguments Build_isomorphic _ _ _ & .
Arguments Build_NaturalTransformation _ _ _ _ & .
Arguments pair _ _ & .
Canonical Structure default_eta {A B} (v : A * B) : A * B := (fst v, snd v).
Canonical Structure pair' {A B} (a : A) (b : B) : A * B := pair a b.

Declare Scope functor_object_scope.
Declare Scope functor_morphism_scope.
Declare Scope natural_transformation_components_scope.
Arguments Build_Functor (C D)%category_scope
& _%functor_object_scope _%functor_morphism_scope (_ _)%function_scope.
Arguments Build_NaturalTransformation [C D]%category_scope (F G)%functor_scope
& _%natural_transformation_components_scope _%function_scope.

Notation "x : A ↦ₒ f"
  := (fun x : A%category => f) (at level 70) : functor_object_scope.
Notation "x ↦ₒ f"
  := (fun x => f) (at level 70) : functor_object_scope.
Notation "' x ↦ₒ f"
  := (fun '(x%category) => f) (x strict pattern, at level 70)
     : functor_object_scope.
Notation "m @ s --> d ↦ₘ f"
  := (fun s d m => f) (at level 70) : functor_morphism_scope.
Notation "' m @ s --> d ↦ₘ f"
  := (fun s d 'm => f) (at level 70, m strict pattern)
     : functor_morphism_scope.
Notation "m : A ↦ₘ f"
  := (fun s d (m : A%category) => f) (at level 70)
     : functor_morphism_scope.
Notation "m ↦ₘ f"
  := (fun s d m => f) (at level 70) : functor_morphism_scope.
Notation "' m ↦ₘ f"
  := (fun s d '(m%category) => f) (m strict pattern, at level 70)
     : functor_morphism_scope.
Notation "x : A ↦ₜ f"
  := (fun x : A%category => f) (at level 70)
     : natural_transformation_components_scope.
Notation "' x ↦ₜ f"
  := (fun '(x%category) => f) (x strict pattern, at level 70)
     : natural_transformation_components_scope.
Notation "x ↦ₜ f"
  := (fun x => f) (at level 70)
     : natural_transformation_components_scope.

Notation "⟨ fo ; mo ⟩"
  := (@Build_Functor _ _ fo mo _ _) (only parsing) : functor_scope.
Notation "⟨ f ⟩"
  := (@Build_NaturalTransformation _ _ _ _ f _) (only parsing)
     : natural_transformation_scope.


Notation "'λ' ⟨ fo ; mo ⟩"
  := (@Build_Functor _ _ fo mo _ _) (only parsing) : functor_scope.
Notation "'λ' ⟨ f ⟩"
  := (@Build_NaturalTransformation _ _ _ _ f _) (only parsing)
     : natural_transformation_scope.

Notation "'λₒ' x1 .. xn , fo ; 'λₘ' m1 .. mn , mo"
  := (@Build_Functor
        _ _
        (fun x1 => .. (fun xn => fo) .. )
        (fun s d => (fun m1 => .. (fun mn => mo) .. ))
        _ _)
       (only parsing, x1 binder, xn binder, m1 binder, mn binder, at level 70)
     : functor_scope.
Notation "'λₜ' x1 .. xn , f"
  := (@Build_NaturalTransformation
        _ _ _ _
        (fun x1 => .. (fun xn => f) .. )
        _)
       (only parsing, x1 binder, xn binder, at level 70)
     : natural_transformation_scope.

(** [(C₁ × C₂ → D) ≅ (C₁ → (C₂ → D))] *)
(** We denote functors by pairs of maps on objects ([↦ₒ]) and
    morphisms ([↦ₘ]), and natural transformations as a single map
    ([↦ₜ]) *)
Time Program Definition curry_iso1 (C₁ C₂ D : Category)
  : (C₁ * C₂ -> D) ≅ (C₁ -> (C₂ -> D)) :>>> Cat
  := {| fwd
        := ⟨ F ↦ₒ ⟨ c₁ ↦ₒ ⟨ c₂ ↦ₒ F ₀  (c₁, c₂)
                          ; m  ↦ₘ F ₁  (identity c₁, m) ⟩
                  ; m₁ ↦ₘ ⟨ c₂ ↦ₜ F ₁  (m₁, identity c₂) ⟩ ⟩
           ; T ↦ₘ ⟨ c₁ ↦ₜ ⟨ c₂ ↦ₜ T (c₁, c₂) ⟩ ⟩ ⟩;
        bwd
        := ⟨ F ↦ₒ ⟨ '(c₁, c₂) ↦ₒ (F ₀  c₁)₀ c₂
                  ; '(m₁, m₂) ↦ₘ (F ₁  m₁) _ ∘ (F ₀  _)₁ m₂ ⟩
           ; T ↦ₘ ⟨ '(c₁, c₂) ↦ₜ (T c₁) c₂ ⟩ ⟩ |}.

(** [(C₁ × C₂ → D) ≅ (C₁ → (C₂ → D))] *)
(** We denote functors by pairs of maps ([λ]) on objects ([↦ₒ]) and
    morphisms ([↦ₘ]), and natural transformations as a single map
    ([λ ⟨ ... ↦ₜ ... ⟩]) *)
Time Program Definition curry_iso2 (C₁ C₂ D : Category)
  : (C₁ * C₂ -> D) ≅ (C₁ -> (C₂ -> D)) :>>> Cat
  := {| fwd
        := λ ⟨ F ↦ₒ λ ⟨ c₁ ↦ₒ λ ⟨ c₂ ↦ₒ F ₀  (c₁, c₂)
                                ; m  ↦ₘ F ₁  (identity c₁, m) ⟩
                      ; m₁ ↦ₘ λ ⟨ c₂ ↦ₜ F ₁  (m₁, identity c₂) ⟩ ⟩
             ; T ↦ₘ λ ⟨ c₁ ↦ₜ λ ⟨ c₂ ↦ₜ T (c₁, c₂) ⟩ ⟩ ⟩;
        bwd
        := λ ⟨ F ↦ₒ λ ⟨ '(c₁, c₂) ↦ₒ (F ₀  c₁)₀ c₂
                      ; '(m₁, m₂) ↦ₘ (F ₁  m₁) _ ∘ (F ₀  _)₁ m₂ ⟩
             ; T ↦ₘ λ ⟨ '(c₁, c₂) ↦ₜ (T c₁) c₂ ⟩ ⟩ |}.

(** [(C₁ × C₂ → D) ≅ (C₁ → (C₂ → D))] *)
(** We denote functors by pairs of maps on objects ([λₒ]) and
    morphisms ([λₘ]), and natural transformations as a single map
    ([λₜ]) *)
Time Program Definition curry_iso3 (C₁ C₂ D : Category)
  : (C₁ * C₂ -> D) ≅ (C₁ -> (C₂ -> D)) :>>> Cat
  := {| fwd
        := λₒ F, λₒ c₁, λₒ c₂, F ₀  (c₁, c₂)
                      ; λₘ m , F ₁  (identity c₁, m)
               ; λₘ m₁, λₜ c₂, F ₁  (m₁, identity c₂)
         ; λₘ T, λₜ c₁, λₜ c₂, T (c₁, c₂);
        bwd
        := λₒ F, λₒ '(c₁, c₂), (F ₀  c₁)₀ c₂
               ; λₘ '(m₁, m₂), (F ₁  m₁) _ ∘ (F ₀  _)₁ m₂
         ; λₘ T, λₜ '(c₁, c₂), (T c₁) c₂ |}.

(** [(C₁ × C₂ → D) ≅ (C₁ → (C₂ → D))] *)
(** We provide the action of functors on objects ([object_of]) and on
    morphisms ([morphism_of]), and we provide the action of natural
    transformations on object ([components_of] *)
Time Program Definition curry_iso (C₁ C₂ D : Category)
  : (C₁ * C₂ -> D) ≅ (C₁ -> (C₂ -> D)) :>>> Cat
  := {| fwd
        := {| object_of F
              := {| object_of c₁
                    := {| object_of      c₂ := F ₀ (c₁, c₂);
                          morphism_of _ _ m := F ₁ (identity c₁, m) |};
                    morphism_of _ _ m₁
                    := {| components_of  c₂ := F ₁ (m₁, identity c₂) |} |};
              morphism_of _ _ T
              := {| components_of c₁
                    := {| components_of  c₂ := T (c₁, c₂) |} |} |};
        bwd
        := {| object_of F
              := {| object_of                       '(c₁, c₂)
                    := (F ₀ c₁)₀ c₂;
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
1 subgoal (ID 1464)

  ============================
  forall C₁ C₂ D : Category,
  {|
  object_of := F
               ↦ₒ {|
                  object_of := pat
                               ↦ₒ
                               (F₀ (fst pat))₀
                               (snd pat);
                  morphism_of := pat1 @ pat -->
                                pat0
                                ↦ₘ
                                (F₁ (fst pat1))
                                (snd pat0)
                                ∘
                                (F₀ (fst pat))₁
                                (snd pat1);
                  composition_of := curry_iso_obligation_7
                                F;
                  identity_of := curry_iso_obligation_8
                                F |};
  morphism_of := T @ s --> d
                 ↦ₘ {|
                    components_of := pat
                                ↦ₜ T (fst pat)
                                (snd pat);
                    commutes := curry_iso_obligation_9
                                T |};
  composition_of := curry_iso_obligation_11
                      (D:=D);
  identity_of := curry_iso_obligation_10 (D:=D) |}
  ∘ {|
    object_of := F
                 ↦ₒ {|
                    object_of := c₁
                                ↦ₒ
                                {|
                                object_of := c₂
                                ↦ₒ F₀ (c₁, c₂);
                                morphism_of := m @
                                s --> d
                                ↦ₘ F₁ (1, m);
                                composition_of := curry_iso_obligation_1
                                F c₁;
                                identity_of := curry_iso_obligation_2
                                F c₁ |};
                    morphism_of := m₁ @ s --> d
                                ↦ₘ {|
                                components_of := c₂
                                ↦ₜ F₁ (m₁, 1);
                                commutes := curry_iso_obligation_3
                                F s d m₁ |};
                    composition_of := curry_iso_obligation_5
                                F;
                    identity_of := curry_iso_obligation_4
                                F |};
    morphism_of := T @ s --> d
                   ↦ₘ {|
                      components_of := c₁
                                ↦ₜ {|
                                components_of := c₂
                                ↦ₜ T (c₁, c₂);
                                commutes := curry_iso_obligation_6
                                T c₁ |};
                      commutes := curry_iso_obligation_12
                                T |};
    composition_of := curry_iso_obligation_14
                        (D:=D);
    identity_of := curry_iso_obligation_13 (D:=D) |} =
  1
 *)
  (** About 48 lines *)
  cbv [compose Cat Functor.compose NaturalTransformation.compose].
  (**
1 subgoal (ID 1469)

  ============================
  forall C₁ C₂ D : Category,
  {|
  object_of := x
               ↦ₒ {|
                  object_of := F
                               ↦ₒ
                               {|
                               object_of := pat
                                ↦ₒ (F₀ (fst pat))₀
                                (snd pat);
                               morphism_of := pat1 @
                                pat --> pat0
                                ↦ₘ (F₁
                                (fst pat1))
                                (snd pat0)
                                ∘ (F₀ (fst pat))₁
                                (snd pat1);
                               composition_of := curry_iso_obligation_7
                                F;
                               identity_of := curry_iso_obligation_8
                                F |};
                  morphism_of := T @ s --> d
                                ↦ₘ
                                {|
                                components_of := pat
                                ↦ₜ T (fst pat)
                                (snd pat);
                                commutes := curry_iso_obligation_9
                                T |};
                  composition_of := curry_iso_obligation_11
                                (D:=D);
                  identity_of := curry_iso_obligation_10
                                (D:=D) |}₀
               ({|
                object_of := F
                             ↦ₒ {|
                                object_of := c₁
                                ↦ₒ {|
                                object_of := c₂
                                ↦ₒ F₀ (c₁, c₂);
                                morphism_of := m @
                                s --> d
                                ↦ₘ F₁ (1, m);
                                composition_of := curry_iso_obligation_1
                                F c₁;
                                identity_of := curry_iso_obligation_2
                                F c₁ |};
                                morphism_of := m₁ @
                                s --> d
                                ↦ₘ {|
                                components_of := c₂
                                ↦ₜ F₁ (m₁, 1);
                                commutes := curry_iso_obligation_3
                                F s d m₁ |};
                                composition_of := curry_iso_obligation_5
                                F;
                                identity_of := curry_iso_obligation_4
                                F |};
                morphism_of := T @ s --> d
                               ↦ₘ
                               {|
                               components_of := c₁
                                ↦ₜ {|
                                components_of := c₂
                                ↦ₜ T (c₁, c₂);
                                commutes := curry_iso_obligation_6
                                T c₁ |};
                               commutes := curry_iso_obligation_12
                                T |};
                composition_of := curry_iso_obligation_14
                                (D:=D);
                identity_of := curry_iso_obligation_13
                                (D:=D) |}₀ x);
  morphism_of := m @ s --> d
                 ↦ₘ {|
                    object_of := F
                                ↦ₒ
                                {|
                                object_of := pat
                                ↦ₒ (F₀ (fst pat))₀
                                (snd pat);
                                morphism_of := pat1 @
                                pat --> pat0
                                ↦ₘ (F₁
                                (fst pat1))
                                (snd pat0)
                                ∘ (F₀ (fst pat))₁
                                (snd pat1);
                                composition_of := curry_iso_obligation_7
                                F;
                                identity_of := curry_iso_obligation_8
                                F |};
                    morphism_of := T @ s0 --> d0
                                ↦ₘ {|
                                components_of := pat
                                ↦ₜ T (fst pat)
                                (snd pat);
                                commutes := curry_iso_obligation_9
                                T |};
                    composition_of := curry_iso_obligation_11
                                (D:=D);
                    identity_of := curry_iso_obligation_10
                                (D:=D) |}₁
                 ({|
                  object_of := F
                               ↦ₒ
                               {|
                               object_of := c₁
                                ↦ₒ {|
                                object_of := c₂
                                ↦ₒ F₀ (c₁, c₂);
                                morphism_of := m0 @
                                s0 --> d0
                                ↦ₘ F₁ (1, m0);
                                composition_of := curry_iso_obligation_1
                                F c₁;
                                identity_of := curry_iso_obligation_2
                                F c₁ |};
                               morphism_of := m₁ @
                                s0 --> d0
                                ↦ₘ {|
                                components_of := c₂
                                ↦ₜ F₁ (m₁, 1);
                                commutes := curry_iso_obligation_3
                                F s0 d0 m₁ |};
                               composition_of := curry_iso_obligation_5
                                F;
                               identity_of := curry_iso_obligation_4
                                F |};
                  morphism_of := T @ s0 --> d0
                                ↦ₘ
                                {|
                                components_of := c₁
                                ↦ₜ {|
                                components_of := c₂
                                ↦ₜ T (c₁, c₂);
                                commutes := curry_iso_obligation_6
                                T c₁ |};
                                commutes := curry_iso_obligation_12
                                T |};
                  composition_of := curry_iso_obligation_14
                                (D:=D);
                  identity_of := curry_iso_obligation_13
                                (D:=D) |}₁ m);
  composition_of := Functor.compose_obligation_1
                      {|
                      object_of := F
                                ↦ₒ {|
                                object_of := pat
                                ↦ₒ (F₀ (fst pat))₀
                                (snd pat);
                                morphism_of := pat1 @
                                pat --> pat0
                                ↦ₘ (F₁
                                (fst pat1))
                                (snd pat0)
                                ∘ (F₀ (fst pat))₁
                                (snd pat1);
                                composition_of := curry_iso_obligation_7
                                F;
                                identity_of := curry_iso_obligation_8
                                F |};
                      morphism_of := T @ s --> d
                                ↦ₘ {|
                                components_of := pat
                                ↦ₜ T (fst pat)
                                (snd pat);
                                commutes := curry_iso_obligation_9
                                T |};
                      composition_of := curry_iso_obligation_11
                                (D:=D);
                      identity_of := curry_iso_obligation_10
                                (D:=D) |}
                      {|
                      object_of := F
                                ↦ₒ {|
                                object_of := c₁
                                ↦ₒ {|
                                object_of := c₂
                                ↦ₒ F₀ (c₁, c₂);
                                morphism_of := m @
                                s --> d
                                ↦ₘ F₁ (1, m);
                                composition_of := curry_iso_obligation_1
                                F c₁;
                                identity_of := curry_iso_obligation_2
                                F c₁ |};
                                morphism_of := m₁ @
                                s --> d
                                ↦ₘ {|
                                components_of := c₂
                                ↦ₜ F₁ (m₁, 1);
                                commutes := curry_iso_obligation_3
                                F s d m₁ |};
                                composition_of := curry_iso_obligation_5
                                F;
                                identity_of := curry_iso_obligation_4
                                F |};
                      morphism_of := T @ s --> d
                                ↦ₘ {|
                                components_of := c₁
                                ↦ₜ {|
                                components_of := c₂
                                ↦ₜ T (c₁, c₂);
                                commutes := curry_iso_obligation_6
                                T c₁ |};
                                commutes := curry_iso_obligation_12
                                T |};
                      composition_of := curry_iso_obligation_14
                                (D:=D);
                      identity_of := curry_iso_obligation_13
                                (D:=D) |};
  identity_of := Functor.compose_obligation_2
                   {|
                   object_of := F
                                ↦ₒ
                                {|
                                object_of := pat
                                ↦ₒ (F₀ (fst pat))₀
                                (snd pat);
                                morphism_of := pat1 @
                                pat --> pat0
                                ↦ₘ (F₁
                                (fst pat1))
                                (snd pat0)
                                ∘ (F₀ (fst pat))₁
                                (snd pat1);
                                composition_of := curry_iso_obligation_7
                                F;
                                identity_of := curry_iso_obligation_8
                                F |};
                   morphism_of := T @ s --> d
                                ↦ₘ
                                {|
                                components_of := pat
                                ↦ₜ T (fst pat)
                                (snd pat);
                                commutes := curry_iso_obligation_9
                                T |};
                   composition_of := curry_iso_obligation_11
                                (D:=D);
                   identity_of := curry_iso_obligation_10
                                (D:=D) |}
                   {|
                   object_of := F
                                ↦ₒ
                                {|
                                object_of := c₁
                                ↦ₒ {|
                                object_of := c₂
                                ↦ₒ F₀ (c₁, c₂);
                                morphism_of := m @
                                s --> d
                                ↦ₘ F₁ (1, m);
                                composition_of := curry_iso_obligation_1
                                F c₁;
                                identity_of := curry_iso_obligation_2
                                F c₁ |};
                                morphism_of := m₁ @
                                s --> d
                                ↦ₘ {|
                                components_of := c₂
                                ↦ₜ F₁ (m₁, 1);
                                commutes := curry_iso_obligation_3
                                F s d m₁ |};
                                composition_of := curry_iso_obligation_5
                                F;
                                identity_of := curry_iso_obligation_4
                                F |};
                   morphism_of := T @ s --> d
                                ↦ₘ
                                {|
                                components_of := c₁
                                ↦ₜ {|
                                components_of := c₂
                                ↦ₜ T (c₁, c₂);
                                commutes := curry_iso_obligation_6
                                T c₁ |};
                                commutes := curry_iso_obligation_12
                                T |};
                   composition_of := curry_iso_obligation_14
                                (D:=D);
                   identity_of := curry_iso_obligation_13
                                (D:=D) |} |} = 1
   *)
  (** About 254 lines *)
  cbn [object_of morphism_of components_of].
  (**
1 subgoal (ID 1471)

  ============================
  forall C₁ C₂ D : Category,
  {|
  object_of := x
               ↦ₒ {|
                  object_of := pat
                               ↦ₒ
                               x₀
                               (fst pat,
                               snd pat);
                  morphism_of := pat1 @ pat -->
                                pat0
                                ↦ₘ
                                x₁
                                (fst pat1, 1)
                                ∘
                                x₁
                                (1, snd pat1);
                  composition_of := curry_iso_obligation_7
                                {|
                                object_of := c₁
                                ↦ₒ {|
                                object_of := c₂
                                ↦ₒ x₀ (c₁, c₂);
                                morphism_of := m @
                                s --> d
                                ↦ₘ x₁ (1, m);
                                composition_of := curry_iso_obligation_1
                                x c₁;
                                identity_of := curry_iso_obligation_2
                                x c₁ |};
                                morphism_of := m₁ @
                                s --> d
                                ↦ₘ {|
                                components_of := c₂
                                ↦ₜ x₁ (m₁, 1);
                                commutes := curry_iso_obligation_3
                                x s d m₁ |};
                                composition_of := curry_iso_obligation_5
                                x;
                                identity_of := curry_iso_obligation_4
                                x |};
                  identity_of := curry_iso_obligation_8
                                {|
                                object_of := c₁
                                ↦ₒ {|
                                object_of := c₂
                                ↦ₒ x₀ (c₁, c₂);
                                morphism_of := m @
                                s --> d
                                ↦ₘ x₁ (1, m);
                                composition_of := curry_iso_obligation_1
                                x c₁;
                                identity_of := curry_iso_obligation_2
                                x c₁ |};
                                morphism_of := m₁ @
                                s --> d
                                ↦ₘ {|
                                components_of := c₂
                                ↦ₜ x₁ (m₁, 1);
                                commutes := curry_iso_obligation_3
                                x s d m₁ |};
                                composition_of := curry_iso_obligation_5
                                x;
                                identity_of := curry_iso_obligation_4
                                x |} |};
  morphism_of := m @ s --> d
                 ↦ₘ {|
                    components_of := pat
                                ↦ₜ m
                                (
                                fst pat,
                                snd pat);
                    commutes := curry_iso_obligation_9
                                {|
                                components_of := c₁
                                ↦ₜ {|
                                components_of := c₂
                                ↦ₜ m (c₁, c₂);
                                commutes := curry_iso_obligation_6
                                m c₁ |};
                                commutes := curry_iso_obligation_12
                                m |} |};
  composition_of := Functor.compose_obligation_1
                      {|
                      object_of := F
                                ↦ₒ {|
                                object_of := pat
                                ↦ₒ (F₀ (fst pat))₀
                                (snd pat);
                                morphism_of := pat1 @
                                pat --> pat0
                                ↦ₘ (F₁
                                (fst pat1))
                                (snd pat0)
                                ∘ (F₀ (fst pat))₁
                                (snd pat1);
                                composition_of := curry_iso_obligation_7
                                F;
                                identity_of := curry_iso_obligation_8
                                F |};
                      morphism_of := T @ s --> d
                                ↦ₘ {|
                                components_of := pat
                                ↦ₜ T (fst pat)
                                (snd pat);
                                commutes := curry_iso_obligation_9
                                T |};
                      composition_of := curry_iso_obligation_11
                                (D:=D);
                      identity_of := curry_iso_obligation_10
                                (D:=D) |}
                      {|
                      object_of := F
                                ↦ₒ {|
                                object_of := c₁
                                ↦ₒ {|
                                object_of := c₂
                                ↦ₒ F₀ (c₁, c₂);
                                morphism_of := m @
                                s --> d
                                ↦ₘ F₁ (1, m);
                                composition_of := curry_iso_obligation_1
                                F c₁;
                                identity_of := curry_iso_obligation_2
                                F c₁ |};
                                morphism_of := m₁ @
                                s --> d
                                ↦ₘ {|
                                components_of := c₂
                                ↦ₜ F₁ (m₁, 1);
                                commutes := curry_iso_obligation_3
                                F s d m₁ |};
                                composition_of := curry_iso_obligation_5
                                F;
                                identity_of := curry_iso_obligation_4
                                F |};
                      morphism_of := T @ s --> d
                                ↦ₘ {|
                                components_of := c₁
                                ↦ₜ {|
                                components_of := c₂
                                ↦ₜ T (c₁, c₂);
                                commutes := curry_iso_obligation_6
                                T c₁ |};
                                commutes := curry_iso_obligation_12
                                T |};
                      composition_of := curry_iso_obligation_14
                                (D:=D);
                      identity_of := curry_iso_obligation_13
                                (D:=D) |};
  identity_of := Functor.compose_obligation_2
                   {|
                   object_of := F
                                ↦ₒ
                                {|
                                object_of := pat
                                ↦ₒ (F₀ (fst pat))₀
                                (snd pat);
                                morphism_of := pat1 @
                                pat --> pat0
                                ↦ₘ (F₁
                                (fst pat1))
                                (snd pat0)
                                ∘ (F₀ (fst pat))₁
                                (snd pat1);
                                composition_of := curry_iso_obligation_7
                                F;
                                identity_of := curry_iso_obligation_8
                                F |};
                   morphism_of := T @ s --> d
                                ↦ₘ
                                {|
                                components_of := pat
                                ↦ₜ T (fst pat)
                                (snd pat);
                                commutes := curry_iso_obligation_9
                                T |};
                   composition_of := curry_iso_obligation_11
                                (D:=D);
                   identity_of := curry_iso_obligation_10
                                (D:=D) |}
                   {|
                   object_of := F
                                ↦ₒ
                                {|
                                object_of := c₁
                                ↦ₒ {|
                                object_of := c₂
                                ↦ₒ F₀ (c₁, c₂);
                                morphism_of := m @
                                s --> d
                                ↦ₘ F₁ (1, m);
                                composition_of := curry_iso_obligation_1
                                F c₁;
                                identity_of := curry_iso_obligation_2
                                F c₁ |};
                                morphism_of := m₁ @
                                s --> d
                                ↦ₘ {|
                                components_of := c₂
                                ↦ₜ F₁ (m₁, 1);
                                commutes := curry_iso_obligation_3
                                F s d m₁ |};
                                composition_of := curry_iso_obligation_5
                                F;
                                identity_of := curry_iso_obligation_4
                                F |};
                   morphism_of := T @ s --> d
                                ↦ₘ
                                {|
                                components_of := c₁
                                ↦ₜ {|
                                components_of := c₂
                                ↦ₜ T (c₁, c₂);
                                commutes := curry_iso_obligation_6
                                T c₁ |};
                                commutes := curry_iso_obligation_12
                                T |};
                   composition_of := curry_iso_obligation_14
                                (D:=D);
                   identity_of := curry_iso_obligation_13
                                (D:=D) |} |} = 1
   *)
  (** About 200 lines *)
Abort.

Import EqNotations.
Axiom to_arrow1_eq
  : forall C₁ C₂ D (F G : Functor C₁ (C₂ -> D))
           (Hoo : forall c₁ c₂, F c₁ c₂ = G c₁ c₂)
           (Hom : forall c₁ s d (m : morphism _ s d),
               (rew [fun s => morphism D s _] (Hoo c₁ s) in
                rew [morphism D _] (Hoo c₁ d) in
                (F c₁)₁ m) = (G c₁)₁ m)
           (Hm : forall s d (m : morphism _ s d) c₂,
               (rew [fun s => morphism D s _] Hoo s c₂ in
                rew Hoo d c₂ in
                (F ₁ m) c₂)
               = (G ₁ m) c₂),
    F = G.
Axiom to_arrow2_eq
  : forall C₁ C₂ C₃ D (F G : Functor C₁ (C₂ -> (C₃ -> D)))
           (Hooo : forall c₁ c₂ c₃, F c₁ c₂ c₃ = G c₁ c₂ c₃)
           (Hoom : forall c₁ c₂ s d (m : morphism _ s d),
               (rew [fun s => morphism D s _] (Hooo c₁ c₂ s) in
                rew [morphism D _] (Hooo c₁ c₂ d) in
                (F c₁ c₂)₁ m) = (G c₁ c₂)₁ m)
           (Hom : forall c₁ s d (m : morphism _ s d) c₂,
               (rew [fun s => morphism D s _] Hooo c₁ s c₂ in
                rew Hooo c₁ d c₂ in
                ((F c₁)₁ m) c₂)
               = ((G c₁)₁ m) c₂)
           (Hm : forall s d (m : morphism _ s d) c₂ c₃,
               (rew [fun s => morphism D s _] Hooo s c₂ c₃ in
                rew Hooo d c₂ c₃ in
                (F ₁ m) c₂ c₃)
               = ((G ₁ m) c₂ c₃)),
    F = G.

Local Ltac unfold_stuff
  := intros;
     cbv [Cat compose prod_category
          Functor.compose NaturalTransformation.compose];
     cbn [object_of morphism_of components_of].

Local Ltac fin_t
  := repeat first [ progress intros
                  | reflexivity
                  | progress cbn
                  | rewrite left_identity
                  | rewrite right_identity
                  | rewrite identity_of
                  | rewrite <- composition_of ].

Next Obligation.
Proof.
  Time solve [ intros; unshelve eapply to_arrow1_eq; unfold_stuff; fin_t ].
  (* Finished transaction in 0.061 secs (0.061u,0.s) (successful) *)
  Undo.
  Time solve [ intros; unfold_stuff; unshelve eapply to_arrow1_eq; fin_t ].
  (* Finished transaction in 0.176 secs (0.176u,0.s) (successful) *)
Qed.

Next Obligation.
Proof.
  Time solve [ intros; unshelve eapply to_arrow2_eq; unfold_stuff; fin_t ].
  (* Finished transaction in 0.085 secs (0.085u,0.s) (successful) *)
  Undo.
  Time solve [ intros; unfold_stuff; unshelve eapply to_arrow2_eq; fin_t ].
  (* Finished transaction in 0.485 secs (0.475u,0.007s) (successful) *)
Qed.
