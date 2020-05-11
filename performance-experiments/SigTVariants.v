Local Set Nonrecursive Elimination Schemes.
Local Set Implicit Arguments.
Declare Scope prim_type_scope.
Delimit Scope prim_type_scope with prim_type.
Declare Scope prim_scope.
Delimit Scope prim_scope with prim.
Declare Scope poly_type_scope.
Delimit Scope poly_type_scope with poly_type.
Declare Scope poly_scope.
Delimit Scope poly_scope with poly.
Declare Scope poly_prim_type_scope.
Delimit Scope poly_prim_type_scope with poly_prim_type.
Declare Scope poly_prim_scope.
Delimit Scope poly_prim_scope with poly_prim.
Module Type ET. End ET.
Module E. End E.
Module TemplatePolymorphic.
  Local Unset Universe Polymorphism.
  Module NonPrim.
    Local Unset Primitive Projections.
    Record prod A B := pair { fst : A ; snd : B }.
    Record sigT {A} (P : A -> Type) := existT { projT1 : A ; projT2 : P projT1 }.
    Definition prod_eta {A B} (x : prod A B) : x = pair (fst x) (snd x).
    Proof. destruct x; reflexivity. Defined.
    Definition sigT_eta {A P} (x : @sigT A P) : x = @existT A P (projT1 x) (projT2 x).
    Proof. destruct x; reflexivity. Defined.
    Module Export Notations.
      Arguments prod (A B)%type.
      Infix "*" := prod : type_scope.
      Add Printing Let prod.
      Arguments pair {A B}%type (_ _)%core.
      Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
      Arguments fst {A B}%type _%core.
      Arguments snd {A B}%type _%core.
      Add Printing Let sigT.
      Arguments existT {A}%type P%type (_ _)%core.
      Arguments projT1 {A P}%type _%core.
      Arguments projT2 {A P}%type _%core.
      Arguments sigT {A}%type P%type.
      Notation "{ x & P }" := (sigT (fun x => P)) : type_scope.
      Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) : type_scope.
      Notation "{ ' pat & P }" := (sigT (fun pat => P)) : type_scope.
      Notation "{ ' pat : A & P }" := (sigT (A:=A) (fun pat => P)) : type_scope.
      Notation "( x ; y )" := (existT _ x y) : core_scope.
    End Notations.
    Module CoreNotations (E : ET). Include Notations. End CoreNotations.
  End NonPrim.
  Module Prim.
    Local Set Primitive Projections.
    Record prod A B := pair { fst : A ; snd : B }.
    Record sigT {A} (P : A -> Type) := existT { projT1 : A ; projT2 : P projT1 }.
    Definition prod_eta {A B} (x : prod A B) : x = pair (fst x) (snd x).
    Proof. reflexivity. Defined.
    Definition sigT_eta {A P} (x : @sigT A P) : x = @existT A P (projT1 x) (projT2 x).
    Proof. reflexivity. Defined.
    Module Export Notations.
      Arguments prod (A B)%prim_type.
      Infix "*" := prod : prim_type_scope.
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
      Notation "{ ' pat & P }" := (sigT (fun pat => P)) : prim_type_scope.
      Notation "{ ' pat : A & P }" := (sigT (A:=A) (fun pat => P)) : prim_type_scope.
      Notation "( x ; y )" := (existT _ x y) : prim_scope.
    End Notations.
    Module CoreNotations (E : ET).
      Arguments prod (A B)%type.
      Infix "*" := prod : type_scope.
      Add Printing Let prod.
      Arguments pair {A B}%type (_ _)%core.
      Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
      Arguments fst {A B}%type _%core.
      Arguments snd {A B}%type _%core.
      Add Printing Let sigT.
      Arguments existT {A}%type P%type (_ _)%core.
      Arguments projT1 {A P}%type _%core.
      Arguments projT2 {A P}%type _%core.
      Arguments sigT {A}%type P%type.
      Notation "{ x & P }" := (sigT (fun x => P)) : type_scope.
      Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) : type_scope.
      Notation "{ ' pat & P }" := (sigT (fun pat => P)) : type_scope.
      Notation "{ ' pat : A & P }" := (sigT (A:=A) (fun pat => P)) : type_scope.
      Notation "( x ; y )" := (existT _ x y) : core_scope.
    End CoreNotations.
  End Prim.
  Module Export Notations.
    Export NonPrim.Notations.
    Export Prim.Notations.
  End Notations.
End TemplatePolymorphic.
Export TemplatePolymorphic.Notations.
Module Polymorphic.
  Local Set Universe Polymorphism.
  Module NonPrim.
    Local Unset Primitive Projections.
    Record prod A B := pair { fst : A ; snd : B }.
    Record sigT {A} (P : A -> Type) := existT { projT1 : A ; projT2 : P projT1 }.
    Definition prod_eta {A B} (x : prod A B) : x = pair (fst x) (snd x).
    Proof. destruct x; reflexivity. Defined.
    Definition sigT_eta {A P} (x : @sigT A P) : x = @existT A P (projT1 x) (projT2 x).
    Proof. destruct x; reflexivity. Defined.    Module Export Notations.
      Arguments prod (A B)%poly_type.
      Infix "*" := prod : poly_type_scope.
      Add Printing Let prod.
      Arguments pair {A B}%poly_type (_ _)%poly.
      Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : poly_scope.
      Arguments fst {A B}%poly_type _%poly.
      Arguments snd {A B}%poly_type _%poly.
      Add Printing Let sigT.
      Arguments existT {A}%poly_type P%poly_type (_ _)%poly.
      Arguments projT1 {A P}%poly_type _%poly.
      Arguments projT2 {A P}%poly_type _%poly.
      Arguments sigT {A}%poly_type P%poly_type.
      Notation "{ x & P }" := (sigT (fun x => P)) : poly_type_scope.
      Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) : poly_type_scope.
      Notation "{ ' pat & P }" := (sigT (fun pat => P)) : poly_type_scope.
      Notation "{ ' pat : A & P }" := (sigT (A:=A) (fun pat => P)) : poly_type_scope.
      Notation "( x ; y )" := (existT _ x y) : poly_scope.
    End Notations.
    Module CoreNotations (E : ET).
      Arguments prod (A B)%type.
      Infix "*" := prod : type_scope.
      Add Printing Let prod.
      Arguments pair {A B}%type (_ _)%core.
      Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
      Arguments fst {A B}%type _%core.
      Arguments snd {A B}%type _%core.
      Add Printing Let sigT.
      Arguments existT {A}%type P%type (_ _)%core.
      Arguments projT1 {A P}%type _%core.
      Arguments projT2 {A P}%type _%core.
      Arguments sigT {A}%type P%type.
      Notation "{ x & P }" := (sigT (fun x => P)) : type_scope.
      Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) : type_scope.
      Notation "{ ' pat & P }" := (sigT (fun pat => P)) : type_scope.
      Notation "{ ' pat : A & P }" := (sigT (A:=A) (fun pat => P)) : type_scope.
      Notation "( x ; y )" := (existT _ x y) : core_scope.
    End CoreNotations.
  End NonPrim.
  Module Prim.
    Local Set Primitive Projections.
    Record prod A B := pair { fst : A ; snd : B }.
    Record sigT {A} (P : A -> Type) := existT { projT1 : A ; projT2 : P projT1 }.
    Definition prod_eta {A B} (x : prod A B) : x = pair (fst x) (snd x).
    Proof. reflexivity. Defined.
    Definition sigT_eta {A P} (x : @sigT A P) : x = @existT A P (projT1 x) (projT2 x).
    Proof. reflexivity. Defined.
    Module Export Notations.
      Arguments prod (A B)%poly_prim_type.
      Infix "*" := prod : poly_prim_type_scope.
      Add Printing Let prod.
      Arguments pair {A B}%poly_prim_type (_ _)%poly_prim.
      Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : poly_prim_scope.
      Arguments fst {A B}%poly_prim_type _%poly_prim.
      Arguments snd {A B}%poly_prim_type _%poly_prim.
      Add Printing Let sigT.
      Arguments existT {A}%poly_prim_type P%poly_prim_type (_ _)%poly_prim.
      Arguments projT1 {A P}%poly_prim_type _%poly_prim.
      Arguments projT2 {A P}%poly_prim_type _%poly_prim.
      Arguments sigT {A}%poly_prim_type P%poly_prim_type.
      Notation "{ x & P }" := (sigT (fun x => P)) : poly_prim_type_scope.
      Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) : poly_prim_type_scope.
      Notation "{ ' pat & P }" := (sigT (fun pat => P)) : poly_prim_type_scope.
      Notation "{ ' pat : A & P }" := (sigT (A:=A) (fun pat => P)) : poly_prim_type_scope.
      Notation "( x ; y )" := (existT _ x y) : poly_prim_scope.
    End Notations.
    Module CoreNotations (E : ET).
      Arguments prod (A B)%type.
      Infix "*" := prod : type_scope.
      Add Printing Let prod.
      Arguments pair {A B}%type (_ _)%core.
      Notation "( x , y , .. , z )" := (pair .. (pair x y) .. z) : core_scope.
      Arguments fst {A B}%type _%core.
      Arguments snd {A B}%type _%core.
      Add Printing Let sigT.
      Arguments existT {A}%type P%type (_ _)%core.
      Arguments projT1 {A P}%type _%core.
      Arguments projT2 {A P}%type _%core.
      Arguments sigT {A}%type P%type.
      Notation "{ x & P }" := (sigT (fun x => P)) : type_scope.
      Notation "{ x : A & P }" := (sigT (A:=A) (fun x => P)) : type_scope.
      Notation "{ ' pat & P }" := (sigT (fun pat => P)) : type_scope.
      Notation "{ ' pat : A & P }" := (sigT (A:=A) (fun pat => P)) : type_scope.
      Notation "( x ; y )" := (existT _ x y) : core_scope.
    End CoreNotations.
  End Prim.
  Module Export Notations.
    Export NonPrim.Notations.
    Export Prim.Notations.
  End Notations.
End Polymorphic.
Export Polymorphic.Notations.
