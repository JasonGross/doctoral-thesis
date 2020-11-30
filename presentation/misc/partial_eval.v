Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Unicode.Utf8.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.
Definition mul (p q : list (Z * Z)) : list (Z * Z) :=
  flat_map (fun '(w, t) =>
    map (fun '(w', t') =>
      (w * w', t * t'))
  q) p.
Fixpoint square (p : list (Z * Z)) : list (Z * Z)
  := match p with
     | [] => []
     | (w, t) :: ts
       => let two_t := 2 * t in
          ((w * w, t * t) :: map (λ '(w', t'), (w * w', two_t * t')) ts)
            ++ square ts
     end.
Definition split (s : Z) (p : list (Z * Z)) : list (Z * Z) * list (Z * Z)
  := let '(hi, lo) := partition (fun '(w, _) => w mod s =? 0) p in
     (lo, map (fun '(w, t) => (w / s, t)) hi).
Definition reduce (s : Z) (c : list (Z * Z)) (p : list (Z * Z)) : list (Z * Z)
  := let '(lo, hi) := split s p in lo ++ mul c hi.
