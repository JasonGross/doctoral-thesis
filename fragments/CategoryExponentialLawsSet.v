Time
  Definition curry_iso_components_set {C₁ C₂ D : Set}
:= ((fun (F : C₁ * C₂ -> D)
     => (fun c₁ c₂ => F (c₁, c₂)) : C₁ -> C₂ -> D),
    (fun (F : C₁ * C₂ -> D)
     => (fun c₁ c₂s c₂d (m₂ : c₂s = c₂d)
         => f_equal F (f_equal2 pair (eq_refl c₁) m₂))),
    (fun (F : C₁ * C₂ -> D)
     => (fun c₁s c₁d (m₁ : c₁s = c₁d) c₂
         => f_equal F (f_equal2 pair m₁ (eq_refl c₂)))),
    (fun F G (T : forall x : C₁ * C₂, F x = G x :> D)
     => (fun c₁ c₂ => T (c₁, c₂))),
    (fun (F : C₁ -> C₂ -> D)
     => (fun '(c₁, c₂) => F c₁ c₂) : C₁ * C₂ -> D),
    (fun (F : C₁ -> C₂ -> D)
     => (fun s d (m : s = d :> C₁ * C₂)
         => eq_trans (f_equal (F _) (f_equal (@snd _ _) m))
                     (f_equal (fun F => F _) (f_equal F (f_equal (@fst _ _) m)))
            : F (fst s) (snd s) = F (fst d) (snd d))),
    (fun F G (T : forall (c₁ : C₁) (c₂ : C₂), F c₁ c₂ = G c₁ c₂ :> D)
     => (fun '(c₁, c₂) => T c₁ c₂)
        : forall '((c₁, c₂) : C₁ * C₂), F c₁ c₂ = G c₁ c₂)).
(* Finished transaction in 0.009 secs (0.009u,0.s) (successful) *)
