Require Import Ltac2.Ltac2.
Require Import Ltac2.Constr.
Require Import Ltac2.Control.
Require Ltac2.Notations.
Require Ltac2.Array.
Require Ltac2.Int.
Require PerformanceExperiments.Ltac2Compat.Array.
Require Import PerformanceExperiments.Ltac2Compat.Constr.
Require Import PerformanceExperiments.make_nested_sig_common.

Module Import WithLtac2.
  Import Ltac2.Notations.

  Ltac2 Type assoc := [ Left | Right ].

  Ltac2 rec int_of_nat n :=
    (lazy_match! n with
    | 0 => 0
    | S ?n => Int.add 1 (int_of_nat n)
     end).

  Ltac2 rec build_gen_proj_prod_unit (n : int) (mkProdT : constr -> constr -> constr) (unitT : constr) (mkproj : constr (* tyA *) -> constr (* tyB *) -> constr (* val *) -> constr) :=
    match Int.lt 0 n with
    | false => (unitT, (fun v => v))
    | true
      => match build_gen_proj_prod_unit (Int.sub n 1) mkProdT unitT mkproj with
         | (ty, term_cps)
           => (mkProdT unitT ty,
               (fun v => term_cps (mkproj unitT ty v)))
         end
    end.

  Ltac2 rec build_gen_proj_prod_unit_goal (n : int) (mkProdT : constr -> constr -> constr) (unitT : constr) (mkproj : constr (* tyA *) -> constr (* tyB *) -> constr (* val *) -> constr) (eqT : constr) :=
    match build_gen_proj_prod_unit n mkProdT unitT mkproj with
    | (ty, term_cps)
      => let term := term_cps (Unsafe.make (Unsafe.Rel 1)) in
         Unsafe.make
           (Unsafe.mkProd
              (Binder.make None ty)
              (Unsafe.make
                 (Unsafe.App eqT (Array.of_list [unitT; term; term]))))
    end.

  Ltac2 extract_one_projection (c : constr) :=
    match Unsafe.kind c with
    | Unsafe.Proj p _ => fun (ty1 : unit -> constr) (ty2 : unit -> constr) (v : constr)
                         => Unsafe.make (Unsafe.Proj p v)
    | Unsafe.App p _ => fun (ty1 : unit -> constr) (ty2 : unit -> constr) (v : constr)
                        => Unsafe.make (Unsafe.App p (Array.of_list [ty1 (); ty2 (); v]))
    | _ => Control.zero (Invalid_argument (Some (Message.of_constr c)))
    end.

  Ltac2 extract_prod_and_projections (c : constr) :=
    match Unsafe.match_Lambda (Unsafe.kind c) with
    | Some l
      => (let (b, body) := l in
          let ty := Binder.type b in
          match Unsafe.kind ty with
          | Unsafe.App t args
            => (t,
                match Unsafe.match_Lambda (Unsafe.kind (Array.get args 1)) with
                | Some _ => true
                | _ => false
                end)
          | _ => Control.zero (Invalid_argument (Some (Message.of_constr ty)))
          end,
          match Unsafe.kind body with
          | Unsafe.App _ args
            => let n := Array.length args in
               (extract_one_projection (Array.get args (Int.sub n 2)),
                extract_one_projection (Array.get args (Int.sub n 1)))
          | _ => Control.zero (Invalid_argument (Some (Message.of_constr body)))
          end)
    | _ => Control.zero (Invalid_argument (Some (Message.of_constr c)))
    end.

  Ltac2 build_goal_gen_gen (n : int) (extract_from : constr) (a : assoc) :=
    let unitT := 'Datatypes.unit in
    let (prod_sig, projs) := extract_prod_and_projections extract_from in
    let (prodT, is_sig) := prod_sig in
    let (mkFstP0, mkSndP0) := projs in
    let eqT := '(@Logic.eq) in
    let mkApp2 f x y := Unsafe.make (Unsafe.App f (Array.of_list [x; y])) in
    let mkApp3 f x y z := Unsafe.make (Unsafe.App f (Array.of_list [x; y; z])) in
    let mkLamConstNoLift x y := Unsafe.make (Unsafe.mkLambda (Binder.make None x) y) in
    let (mkProdT0, mkFstP, mkSndP)
        := match is_sig with
           | true
             => ((fun x y => mkApp2 prodT x (mkLamConstNoLift x y)),
                 (fun tyx tyy v => mkFstP0 (fun () => tyx) (fun () => mkLamConstNoLift tyx tyy) v),
                 (fun tyx tyy v => mkSndP0 (fun () => tyx) (fun () => mkLamConstNoLift tyx tyy) v))
           | false
             => ((fun x y => mkApp2 prodT x y),
                 (fun tyx tyy v => mkFstP0 (fun () => tyx) (fun () => tyy) v),
                 (fun tyx tyy v => mkSndP0 (fun () => tyx) (fun () => tyy) v))
           end in
    let (mkProdT, mkproj)
        := match a with
           | Left
             => ((fun uni v => mkProdT0 v uni),
                 (fun tyUni tyV v => mkFstP tyV tyUni v))
           | Right
             => ((fun uni v => mkProdT0 uni v),
                 (fun tyUni tyV v => mkSndP tyUni tyV v))
           end in
    build_gen_proj_prod_unit_goal n mkProdT unitT mkproj eqT.

  Ltac2 build_goal_gen (n : int) (a : assoc) :=
    build_goal_gen_gen n '(fun x : Datatypes.prod unit unit => (Datatypes.fst x, Datatypes.snd x)) a.

  Ltac2 build_goal_sig_gen (n : int) (a : assoc) :=
    build_goal_gen_gen n '(fun x : @Specif.sigT unit (fun _ => unit) => (Specif.projT1 x, Specif.projT2 x)) a.

  Ltac2 time_solve_goal_gen (f : int -> assoc -> constr) (n : constr) (a : assoc) :=
    let n := int_of_nat n in
    let v := Control.time
               (Some "build-and-typecheck")
               (fun _ =>
                  let v := Control.time (Some "build") (fun _ => f n a) in
                  let __ := Control.time (Some "check") (fun _ => Unsafe.check v) in
                  let __ := Control.time (Some "type") (fun _ => Constr.type v) in
                  v) in
    Control.time (Some "refine") (fun _ => refine v).

  Ltac2 time_solve_goal_1 n := time_solve_goal_gen build_goal_gen n Left.
  Ltac2 time_solve_goal_2 n := time_solve_goal_gen build_goal_gen n Right.
  Ltac2 time_solve_goal_sig_1 n := time_solve_goal_gen build_goal_sig_gen n Left.
  Ltac2 time_solve_goal_sig_2 n := time_solve_goal_gen build_goal_sig_gen n Right.

  Ltac time_solve_goal_1 :=
    ltac2:(n |- time_solve_goal_1 (match (Ltac1.to_constr n) with Some v => v | None => 'I end)).
  Ltac time_solve_goal_2 :=
    ltac2:(n |- time_solve_goal_2 (match (Ltac1.to_constr n) with Some v => v | None => 'I end)).
  Ltac time_solve_goal_sig_1 :=
    ltac2:(n |- time_solve_goal_sig_1 (match (Ltac1.to_constr n) with Some v => v | None => 'I end)).
  Ltac time_solve_goal_sig_2 :=
    ltac2:(n |- time_solve_goal_sig_2 (match (Ltac1.to_constr n) with Some v => v | None => 'I end)).

  Module Prim.
    Ltac2 build_goal_gen (n : int) (a : assoc) :=
      build_goal_gen_gen n '(fun x : Prim.prod unit unit => (Prim.fst x, Prim.snd x)) a.

    Ltac2 build_goal_sig_gen (n : int) (a : assoc) :=
      build_goal_gen_gen n '(fun x : @Prim.sigT unit (fun _ => unit) => (Prim.projT1 x, Prim.projT2 x)) a.

    Ltac2 time_solve_goal_1 n := time_solve_goal_gen build_goal_gen n Left.
    Ltac2 time_solve_goal_2 n := time_solve_goal_gen build_goal_gen n Right.
    Ltac2 time_solve_goal_sig_1 n := time_solve_goal_gen build_goal_sig_gen n Left.
    Ltac2 time_solve_goal_sig_2 n := time_solve_goal_gen build_goal_sig_gen n Right.

    Ltac time_solve_goal_1 :=
      ltac2:(n |- time_solve_goal_1 (match (Ltac1.to_constr n) with Some v => v | None => 'I end)).
    Ltac time_solve_goal_2 :=
      ltac2:(n |- time_solve_goal_2 (match (Ltac1.to_constr n) with Some v => v | None => 'I end)).
    Ltac time_solve_goal_sig_1 :=
      ltac2:(n |- time_solve_goal_sig_1 (match (Ltac1.to_constr n) with Some v => v | None => 'I end)).
    Ltac time_solve_goal_sig_2 :=
      ltac2:(n |- time_solve_goal_sig_2 (match (Ltac1.to_constr n) with Some v => v | None => 'I end)).
  End Prim.
End WithLtac2.
