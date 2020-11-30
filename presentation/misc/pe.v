
Axiom hide : forall {T} {v : T}, True.
Time Compute @hide _ (fun f g => ModOpsAx.addmod 51 2 5 (expand_list 0 f 5) (expand_list 0 g 5)).
Print ModOpsAx.carry_squaremod.
Require Import UnsaturatedSolinasHeuristics.
Compute (carry_chains 2 (2^127) [(1,1)]).
Require Import Coq.Lists.List.
Import ListNotations.
Compute fun x y => ModOpsAx.carry_squaremod 64 1 (2^127) [(1,1)] 2 [0; 1;0; 1]%nat [x; y].
Goal forall x y,
       let a : Z := y in
       let a1 : Z := (y * 2) in
       let a2 : Z := x in
       let a5 : Z := (2 * (y * a)) in
       let a6 : Z := (x * a1) in
       let a7 : Z := (x * x) in
       let a8 : Z := (a7 + a5) in
       let a9 : Z := (a8 / 18446744073709551616) in
       let a10 : Z := (a8 mod 18446744073709551616) in
       let a11 : Z := (a6) in
       let a12 : Z := a10 in
       let a13 : Z := a9 in
       let a14 : Z := 0 in
       let a15 : Z := (a13 + (a11)) in
       let a16 : Z := (a12) in
       let a17 : Z := (a15) in
       let a18 : Z := (a17 / 18446744073709551616) in
       let a19 : Z := (a17 mod 18446744073709551616) in
       let a20 : Z := a19 in
       let a21 : Z := a18 in
       let a22 : Z := (a16) in
       let a23 : Z := (2 * ( (a21))) in
       let a24 : Z := (a20) in
       let a25 : Z := (a22) in
       let a26 : Z := (a25 + (a23)) in
       let a27 : Z := (a26 / 18446744073709551616) in
       let a28 : Z := (a26 mod 18446744073709551616) in
       let a29 : Z := (a24) in
       let a30 : Z := a28 in
       let a31 : Z := a27 in
       let a32 : Z := 0 in
       let a33 : Z := (a31 + (a29)) in
       let a34 : Z := (a30) in
       let a35 : Z := (a33) in
       let a36 : Z := (a35 / 18446744073709551616) in
       let a37 : Z := (a35 mod 18446744073709551616) in
       let a38 : Z := a37 in
       let a39 : Z := a36 in
       let a40 : Z := (a34) in
       let a41 : Z := (2 * ( (a39))) in
       let a42 : Z := a38 in
       let a43 : Z := a40 in
                           [a43 + a41; a42] = [a43 + a41; a42].

repeat intro.
repeat match goal with
       | [ x := ?y |- _ ] => is_var y; subst x
       | [ x := _ |- _ ] => clear x
       end.
Definition two64 := 18446744073709551616.
change 18446744073709551616 with two64 in *.
Notation "'2⁶⁴'" := two64.
repeat match goal with
       | [ x := _ |- _ ] => revert x
       end.
repeat let x := fresh "a" in intro x.
repeat match goal with
       | [ x := _ |- _ ] => revert x
       end.

  x, y : Z
  ============================
  let a := y * 2 in
  let a0 := 2 * (y * y) in
  let a1 := x * a in
  let a2 := x * x in
  let a3 := a2 + a0 in
  let a4 := a3 / 2⁶⁴ in
  let a5 := a3 mod 2⁶⁴ in
  let a6 := a4 + a1 in
  let a7 := a6 / 2⁶⁴ in
  let a8 := a6 mod 2⁶⁴ in
  let a9 := 2 * a7 in
  let a10 := a5 + a9 in
  let a11 := a10 / 2⁶⁴ in
  let a12 := a10 mod 2⁶⁴ in
  let a13 := a11 + a8 in
  let a14 := a13 / 2⁶⁴ in
  let a15 := a13 mod 2⁶⁴ in
  let a16 := 2 * a14 in [a12 + a16; a15] = [a12 + a16; a15]
