Require Import PerformanceExperiments.SigTVariants.
Require Import PerformanceExperiments.DynList.

Import SigTVariants.TemplatePolymorphic.

Ltac cache_term T v name :=
  let H := fresh in
  let T := constr:(T) in
  let __ := lazymatch constr:(Set) with
            | _
              => simple refine (let H : T := _ in _);
                 [ transparent_abstract exact v using name
                 | ]
            end in
  lazymatch goal with
  | [ H := ?v |- _ ]
    => let __ := match goal with _ => clear H end in
       v
  end.

Local Open Scope dyn_scope.
Ltac make_Ts count mkSigT mkExistT mkProjT1 mkProjT2 mkSigTEta cont :=
  let hd x := lazymatch x with ?v :: _ => v end in
  lazymatch count with
  | 0
    => let _T       := fresh "_T0" in
       let _Build_T := fresh "Build_T0" in
       let _T_proj1 := fresh "_proj1_T0" in
       let _T_proj2 := fresh "_proj2_T0" in
       let _T_eta   := fresh "_eta_T0" in
       let _T_ty       := constr:(Set) in
       let _T          := cache_term _T_ty
                                     unit
                                     _T in
       let _Build_T_ty := constr:(unit -> _T) in
       let _Build_T    := cache_term _Build_T_ty
                                     (fun x0 : unit => x0)
                                     _Build_T in
       let _T_proj_ty  := constr:(_T -> unit) in
       let _T_proj1    := cache_term _T_proj_ty
                                     (fun x0 : _T => x0)
                                     _T_proj1 in
       let _T_proj2    := cache_term _T_proj_ty
                                     (fun x0 : _T => x0)
                                     _T_proj2 in
       let _T_eta_ty   := constr:(forall x : _T, x = _Build_T (_T_proj1 x) :> _T) in
       let _T_eta      := cache_term _T_eta_ty
                                     (fun x : _T => @eq_refl _T x)
                                     _T_eta in
       cont (@DynList.cons _T_ty _T DynList.nil)
            (@DynList.cons _Build_T_ty _Build_T DynList.nil)
            (@DynList.cons _T_proj_ty _T_proj1 DynList.nil)
            (@DynList.cons _T_proj_ty _T_proj2 DynList.nil)
            (@DynList.cons _T_eta_ty _T_eta DynList.nil)
  | S ?count
    => let cont' _Ts _Build_Ts _T_proj1s _T_proj2s _T_etas
           := let _T'       := hd _Ts in
              let _Build_T' := hd _Build_Ts in
              let _T_proj1' := hd _T_proj1s in
              let _T_proj2' := hd _T_proj2s in
              let _T_eta'   := hd _T_etas in
              let _T       := fresh "_T0" in
              let _Build_T := fresh "Build_T0" in
              let _T_proj1 := fresh "_proj1_T0" in
              let _T_proj2 := fresh "_proj2_T0" in
              let _T_eta   := fresh "_eta_T0" in
              let _T_ty       := constr:(Set) in
              let _T_v        := mkSigT unit _T' in
              let _T          := cache_term _T_ty
                                            _T_v
                                            _T in
              let _Build_T_ty := constr:(unit -> _T' -> _T) in
              let _Build_T_v  := mkExistT unit _T' in
              let _Build_T    := cache_term _Build_T_ty
                                            _Build_T_v
                                            _Build_T in
              let _T_proj1_ty := constr:(_T -> unit) in
              let _T_proj1_v  := mkProjT1 unit _T' in
              let _T_proj1    := cache_term _T_proj1_ty
                                            _T_proj1_v
                                            _T_proj1 in
              let _T_proj2_ty := constr:(_T -> _T') in
              let _T_proj2_v  := mkProjT2 unit _T' in
              let _T_proj2    := cache_term _T_proj2_ty
                                            _T_proj2_v
                                            _T_proj2 in
              let _T_eta_ty   := constr:(forall x : _T, x = _Build_T (_T_proj1 x) (_T_proj2 x) :> _T) in
              let _T_eta_v    := mkSigTEta unit _T' in
              let _T_eta      := cache_term _T_eta_ty
                                            _T_eta_v
                                            _T_eta in
              cont (@DynList.cons _T_ty _T _Ts)
                   (@DynList.cons _Build_T_ty _Build_T _Build_Ts)
                   (@DynList.cons _T_proj1_ty _T_proj1 _T_proj1s)
                   (@DynList.cons _T_proj2_ty _T_proj2 _T_proj2s)
                   (@DynList.cons _T_eta_ty _T_eta _T_etas) in
       make_Ts count mkSigT mkExistT mkProjT1 mkProjT2 mkSigTEta cont'
  end.

Ltac make_T _Ts :=
  let hd x := lazymatch x with ?v :: _ => v end in
  let tl x := lazymatch x with _ :: ?v => v end in
  let T := fresh "T" in
  let _T' := hd _Ts in
  cache_term Set _T' T.

Ltac make_T_projs T _Ts _T_proj1s _T_proj2s proj_T_rest' cont :=
  let hd x := lazymatch x with ?v :: _ => v end in
  let tl x := lazymatch x with _ :: ?v => v end in
  let _T'_proj1 := hd _T_proj1s in
  let _T_proj1s := tl _T_proj1s in
  let proj_T      := fresh "proj_T_1" in
  let proj_T_ty      := constr:(T -> unit) in
  let proj_T_v       := constr:(fun x : T => _T'_proj1 (proj_T_rest' x)) in
  let proj_T         := cache_term proj_T_ty proj_T_v proj_T in
  lazymatch _Ts with
  | DynList.nil
    => cont (@DynList.cons proj_T_ty proj_T DynList.nil) DynList.nil
  | ?_T :: ?_Ts
    => let _T'_proj2 := hd _T_proj2s in
       let _T_proj2s := tl _T_proj2s in
       let proj_T_rest := fresh "proj_T_rest_1" in
       let proj_T_rest_ty := constr:(T -> _T) in
       let proj_T_rest_v  := constr:(fun x : T => _T'_proj2 (proj_T_rest' x)) in
       let proj_T_rest    := cache_term proj_T_rest_ty proj_T_rest_v proj_T_rest in
       let cont' proj_Ts proj_T_rests
           := cont (@DynList.cons proj_T_ty proj_T proj_Ts)
                   (@DynList.cons proj_T_rest_ty proj_T_rest proj_T_rests) in
       make_T_projs T _Ts _T_proj1s _T_proj2s proj_T_rest cont'
  end.

Ltac make_Build_T_ty T _Build_Ts :=
  lazymatch _Build_Ts with
  | [] => T
  | _ :: ?_Build_Ts
    => let res := make_Build_T_ty T _Build_Ts in
       uconstr:(unit -> res)
  end.

Ltac make_Build_T T _Build_Ts :=
  let Build_T_ty := make_Build_T_ty T _Build_Ts in
  let __ := match goal with
            | _ => simple refine (let H : Build_T_ty := _ in
                                  _);
                   [ let rec iter _Build_Ts cont :=
                         let x := fresh "x" in
                         intro x;
                         lazymatch _Build_Ts with
                         | [?_Build_T] => cont uconstr:(_Build_T x)
                         | ?_Build_T :: ?_Build_Ts
                           => iter _Build_Ts ltac:(fun res => cont uconstr:(_Build_T x res))
                         end in
                     iter _Build_Ts ltac:(fun res => refine res)
                   | ]
            end in
  lazymatch goal with
  | [ H := ?v |- _ ]
    => let __ := match goal with _ => clear H end in
       let Build_T := fresh "Build_T" in
       (** Work around COQBUG(https://github.com/coq/coq/issues/12298) *)
       let v := (eval cbv beta in v) in
       cache_term Build_T_ty v Build_T
  end.

Ltac make_T_eta_ty T Build_T proj_Ts :=
  let hd x := lazymatch x with ?v :: _ => v end in
  let tl x := lazymatch x with _ :: ?v => v end in
  let x := fresh "x" in
  constr:(forall x : T,
             ltac:(let rec iter proj_Ts cur :=
                       lazymatch proj_Ts with
                       | [] => cur
                       | ?proj_T :: ?proj_Ts
                         => iter proj_Ts uconstr:(cur (proj_T x))
                       end in
                   let v := iter proj_Ts Build_T in
                   refine (x = v :> T))).

Ltac make_T_eta_prim T Build_T proj_Ts :=
  let T_eta := fresh "T_eta" in
  let T_eta_ty := make_T_eta_ty T Build_T proj_Ts in
  cache_term T_eta_ty constr:(@eq_refl T) T_eta.

Ltac make_T_eta_nonprim T Build_T proj_Ts _Ts _T_proj1s _T_proj2s _Build_Ts _T_etas :=
  let hd x := lazymatch x with ?v :: _ => v end in
  let tl x := lazymatch x with _ :: ?v => v end in
  let T_eta_ty := make_T_eta_ty T Build_T proj_Ts in
  lazymatch T_eta_ty with
  | forall x : _, ?P
    => let x' := fresh in
       let P' := fresh in
       let T_eta_v
           := constr:(
                fun x : T
                => match x, P return P with
                   | x', P'
                     => ltac:(
                          let x := (eval cbv delta [x'] in x') in
                          let P := (eval cbv delta [P'] in P') in
                          clear x' P';
                          restart_timer "eta-make-let-ins";
                          let rec make_lhss _T_proj2s prev_lhs :=
                              let _T_proj2  := hd _T_proj2s in
                              let _T_proj2s := tl _T_proj2s in
                              let lhs := fresh "lhs" in
                              let lhs_v  := constr:(_T_proj2 prev_lhs) in
                              let lhs_T := type of lhs_v in
                              let lhs := cache_term lhs_T lhs_v lhs in
                              let rest :=
                                  lazymatch _T_proj2s with
                                  | [] => DynList.nil
                                  | _ :: _ => make_lhss _T_proj2s lhs
                                  end in
                              uconstr:(@DynList.cons lhs_T lhs rest) in
                          let lhss := let _T := hd _Ts in
                                      let _T_proj2s := constr:(@DynList.cons (T -> _T) (fun x : T => (x : _T)) _T_proj2s) in
                                      let v := make_lhss _T_proj2s x in
                                      constr:(v) in
                          (*idtac lhss;*)
                          let rec make_rhss _T_proj1s _Build_Ts lhss :=
                              let _Build_T  := hd _Build_Ts in
                              let _Build_Ts := tl _Build_Ts in
                              let _T_proj1  := hd _T_proj1s in
                              let _T_proj1s := tl _T_proj1s in
                              let lhs  := hd lhss in
                              let lhss := tl lhss in
                              lazymatch lhss with
                              | [?final]
                                => let rhs := fresh "rhs" in
                                   (* let rhs0 := Build_T0 final in *)
                                   let rhs_v  := constr:(_Build_T lhs) in
                                   let rhs_ty := type of rhs_v in
                                   let rhs := cache_term rhs_ty rhs_v rhs in
                                   constr:(@DynList.cons rhs_ty rhs DynList.nil)
                              | _ :: _
                                => let rhss := make_rhss _T_proj1s _Build_Ts lhss in
                                   let prev_rhs := hd rhss in
                                   let rhs := fresh "rhs" in
                                   let rhs_v  := constr:(_Build_T (_T_proj1 lhs) prev_rhs) in
                                   let rhs_ty := type of rhs_v in
                                   let rhs := cache_term rhs_ty rhs_v rhs in
                                   constr:(@DynList.cons rhs_ty rhs rhss)
                              end in
                          let rhss := make_rhss _T_proj1s _Build_Ts lhss in
                          finish_timing ("Tactic call") "eta-make-let-ins";
                          (*idtac rhss;*)
                          let rec iter_eq _Ts lhss rhss _Build_Ts _T_proj1s _T_etas :=
                              let _T  := hd _Ts in
                              let _Ts := tl _Ts in
                              let lhs  := hd lhss in
                              let lhss := tl lhss in
                              let rhs  := hd rhss in
                              let rhss := tl rhss in
                              let _Build_T  := hd _Build_Ts in
                              let _Build_Ts := tl _Build_Ts in
                              let _T_proj1  := hd _T_proj1s in
                              let _T_proj1s := tl _T_proj1s in
                              let _T_eta  := hd _T_etas in
                              let _T_etas := tl _T_etas in
                              let eta_pf := uconstr:(_T_eta lhs) in
                              lazymatch _Ts with
                              | []
                                => eta_pf
                              | _ :: _
                                => let _T' := hd _Ts in
                                   let lhs' := hd lhss in
                                   let rhs' := hd rhss in
                                   let rest_pf := iter_eq _Ts lhss rhss _Build_Ts _T_proj1s _T_etas in
                                   let builder := uconstr:(_Build_T (_T_proj1 lhs)) in
                                   uconstr:(
                                     (@eq_trans _T)
                                       lhs (builder lhs') rhs
                                       eta_pf
                                       (@f_equal
                                          _T' _T
                                          builder
                                          lhs' rhs'
                                          rest_pf))
                              end in
                          let pf := let __ := match goal with _ => restart_timer "eta-make-pf" end in
                                    let pf := iter_eq _Ts lhss rhss _Build_Ts _T_proj1s _T_etas in
                                    let __ := match goal with _ => finish_timing ("Tactic call") "eta-make-pf" end in
                                    let __ := match goal with _ => restart_timer "eta-constr-pf" end in
                                    let pf := constr:(pf) in
                                    let __ := match goal with _ => finish_timing ("Tactic call") "eta-constr-pf" end in
                                    pf in
                          (*idtac pf;*)
                          restart_timer "eta-cast-pf";
                          let pf_casted := constr:(pf : P) in
                          finish_timing ( "Tactic call" ) "eta-cast-pf";
                          restart_timer "eta-refine-and-close";
                          time "eta-refine" refine pf_casted
                        )
                   end) in
       let __ := match goal with _ => finish_timing ( "Tactic call" ) "eta-refine-and-close" end in
       let T_eta := fresh "T_eta" in
       cache_term T_eta_ty T_eta_v T_eta
  end.

Ltac make_T_eta prim T Build_T proj_Ts _Ts _T_proj1s _T_proj2s _Build_Ts _T_etas :=
  lazymatch prim with
  | true => make_T_eta_prim T Build_T proj_Ts
  | false => make_T_eta_nonprim T Build_T proj_Ts _Ts _T_proj1s _T_proj2s _Build_Ts _T_etas
  end.

Ltac make_f_ty T Build_T proj_Ts :=
  let __ := match goal with _ => restart_timer "make_f_ty" end in
  let TYPE := constr:(Type) in
  let __ :=
      match goal with
      | _
        => let H := fresh in
           let P := fresh "P" in
           simple refine (let H : (T -> Type) -> TYPE := fun (P : T -> Type) => _ in
                          _);
           [ let rec iter proj_Ts fx :=
                 lazymatch proj_Ts with
                 | [] => refine (P fx)
                 | _ :: ?proj_Ts
                   => let x := fresh "x" in
                      let fx' := fresh in
                      let res
                          := constr:(
                               forall (x : unit),
                                 match fx x return TYPE with
                                 | fx'
                                   => ltac:(clearbody fx';
                                            try clear fx;
                                            iter proj_Ts fx')
                                 end) in
                      refine res
                 end in
             iter proj_Ts Build_T
           | ]
      end in
  lazymatch goal with
  | [ H := ?v |- _ ]
    => let __ := match goal with _ => clear H end in
       let __ := match goal with _ => finish_timing ( "Tactic call" ) "make_f_ty" end in
       v
  end.

Import EqNotations.
Ltac make_T_rect T Build_T proj_Ts T_eta :=
  let hd x := lazymatch x with ?v :: _ => v end in
  let tl x := lazymatch x with _ :: ?v => v end in
  let f_ty := make_f_ty T Build_T proj_Ts in
  lazymatch f_ty with
  | fun P' => ?f_ty
    => let P := fresh "P" in
       let f := fresh "f" in
       let x := fresh "x" in
       let T_rect_v
           := constr:(fun (P : T -> Type) (f : match P with P' => f_ty end) (x : T)
                      => ((rew <- [P] T_eta x in
                              ltac:(let rec iter proj_Ts fx :=
                                        lazymatch proj_Ts with
                                        | [] => fx
                                        | ?proj_T :: ?proj_Ts
                                          => iter proj_Ts uconstr:(fx (proj_T x))
                                        end in
                                    let res := iter proj_Ts f in
                                    refine res))
                          : P x)) in
       let T_rect_ty := type of T_rect_v in
       let T_rect := fresh "T_rect" in
       cache_term T_rect_ty T_rect_v T_rect
  end.

Ltac make_final_goal T proj_Ts :=
  let rec last ls :=
      match ls with
      | [?v] => v
      | _ :: ?ls => last ls
      end in
  let proj_T := last proj_Ts in
  let __ := match goal with _ => restart_timer "make_final_goal" end in
  let res := constr:(forall x : T, proj_T x = proj_T x :> unit) in
  let __ := match goal with _ => finish_timing ( "Tactic call constr-final-goal" ) "make_final_goal" end in
  res.

Ltac destruct_in_final_goal T_rect :=
  time "final-destruct"
       (idtac;
        lazymatch goal with
        | [ |- forall x, @?P x ]
          => time "final-refine" refine (T_rect P _);
             time "final-intros" intros
        end).

Inductive PrimStatus := Prim | NonPrim.
Inductive SigOrProd := Sig | Prod.

Ltac make_record prim_status sig_or_prod :=
  let hd x := lazymatch x with ?v :: _ => v end in
  let tl x := lazymatch x with _ :: ?v => v end in
  let with_data
      := lazymatch constr:((prim_status, sig_or_prod)) with
         | (Prim, Sig)
           => let prim := constr:(true) in
              let mkSigT A B := constr:(@Prim.sigT A (fun _ : A => B)) in
              let mkExistT A B := constr:(@Prim.existT A (fun _ : A => B)) in
              let mkProjT1 A B := constr:(fun x : @Prim.sigT A (fun _ : A => B) => Prim.projT1 x) in
              let mkProjT2 A B := constr:(fun x : @Prim.sigT A (fun _ : A => B) => Prim.projT2 x) in
              let mkSigTEta A B := constr:(@Prim.sigT_eta A (fun _ : A => B)) in
              fun cont => cont prim mkSigT mkExistT mkProjT1 mkProjT2 mkSigTEta
         | (Prim, Prod)
           => let prim := constr:(true) in
              let mkSigT A B := constr:(@Prim.prod A B) in
              let mkExistT A B := constr:(@Prim.pair A B) in
              let mkProjT1 A B := constr:(fun x : @Prim.prod A B => Prim.fst x) in
              let mkProjT2 A B := constr:(fun x : @Prim.prod A B => Prim.snd x) in
              let mkSigTEta A B := constr:(@Prim.prod_eta A B) in
              fun cont => cont prim mkSigT mkExistT mkProjT1 mkProjT2 mkSigTEta
         | (NonPrim, Sig)
           => let prim := constr:(false) in
              let mkSigT A B := constr:(@NonPrim.sigT A (fun _ : A => B)) in
              let mkExistT A B := constr:(@NonPrim.existT A (fun _ : A => B)) in
              let mkProjT1 A B := constr:(fun x : @NonPrim.sigT A (fun _ : A => B) => @NonPrim.projT1 A (fun _ : A => B) x) in
              let mkProjT2 A B := constr:(fun x : @NonPrim.sigT A (fun _ : A => B) => @NonPrim.projT2 A (fun _ : A => B) x) in
              let mkSigTEta A B := constr:(@NonPrim.sigT_eta A (fun _ : A => B)) in
              fun cont => cont prim mkSigT mkExistT mkProjT1 mkProjT2 mkSigTEta
         | (NonPrim, Prod)
           => let prim := constr:(false) in
              let mkSigT A B := constr:(@NonPrim.prod A B) in
              let mkExistT A B := constr:(@NonPrim.pair A B) in
              let mkProjT1 A B := constr:(fun x : @NonPrim.prod A B => @NonPrim.fst A B x) in
              let mkProjT2 A B := constr:(fun x : @NonPrim.prod A B => @NonPrim.snd A B x) in
              let mkSigTEta A B := constr:(@NonPrim.prod_eta A B) in
              fun cont => cont prim mkSigT mkExistT mkProjT1 mkProjT2 mkSigTEta
         | ?status
           => fun cont n => fail 0 "Invalid status" status
         end in
  with_data
    ltac:(
    fun prim mkSigT mkExistT mkProjT1 mkProjT2 mkSigTEta
    => let cont _Ts _Build_Ts _T_proj1s _T_proj2s _T_etas :=
           let __ := match goal with _ => finish_timing ( "Tactic call" ) "make_Ts" end in
           let __ := match goal with _ => restart_timer "make_T" end in
           let T := make_T _Ts in
           let __ := match goal with _ => finish_timing ( "Tactic call" ) "make_T" end in
           let _T := hd _Ts in
           let _Ts' := tl _Ts in
           let cont proj_Ts proj_T_rests :=
               let __ := match goal with _ => finish_timing ( "Tactic call" ) "make_T_projs" end in
               let __ := match goal with _ => restart_timer "make_Build_T" end in
               let Build_T := make_Build_T T _Build_Ts in
               let __ := match goal with _ => finish_timing ( "Tactic call" ) "make_Build_T" end in
               let __ := match goal with _ => restart_timer "make_T_eta" end in
               let T_eta := make_T_eta prim T Build_T proj_Ts _Ts _T_proj1s _T_proj2s _Build_Ts _T_etas in
               let __ := match goal with _ => finish_timing ( "Tactic call" ) "make_T_eta" end in
               let __ := match goal with _ => restart_timer "make_T_rect" end in
               let T_rect := make_T_rect T Build_T proj_Ts T_eta in
               let __ := match goal with _ => finish_timing ( "Tactic call" ) "make_T_rect" end in
               let __ := match goal with _ => finish_timing ( "Tactic call" ) "making" end in
               let goal := make_final_goal T proj_Ts in
               try (solve [ assert goal;
                            [ once destruct_in_final_goal
                            | ] ]; [])
           (*idtac T proj_Ts Build_T T_eta proj_T_rests _Ts _Build_Ts _T_proj1s _T_proj2s _T_etas*) in
           let __ := match goal with _ => restart_timer "make_T_projs" end in
           make_T_projs T _Ts' _T_proj1s _T_proj2s constr:(fun x : T => x) cont in
       let tac n :=
           once (
               let __ := match goal with _ => restart_timer "make_Ts" end in
               let __ := match goal with _ => restart_timer "making" end in
               make_Ts n mkSigT mkExistT mkProjT1 mkProjT2 mkSigTEta cont) in
       fun n => tac n).

Ltac do_prim_prod := make_record Prim Prod.
Ltac do_prod := make_record NonPrim Prod.
Ltac do_prim_sig := make_record Prim Sig.
Ltac do_sig := make_record NonPrim Sig.
