Inductive is_even : nat -> Prop :=
| zero_even : is_even 0
| two_plus_even n : is_even n -> is_even (S (S n)).
Inductive parity := even | odd.
Definition flip_parity p
  := match p with even => odd | odd => even end.
Fixpoint parity_of (n : nat) : parity :=
  match n with
  | O => even
  | S n' => flip_parity (parity_of n')
  end.
Lemma parity_of_correct_helper
  : forall n, match parity_of n with
              | even => is_even n
              | odd => is_even (S n)
              end.
Proof.
  induction n as [|n IH]; cbn; try constructor.
  destruct (parity_of n); cbn; try constructor; try assumption.
Qed.
Lemma parity_of_correct : forall n, parity_of n = even -> is_even n.
Proof.
  intros n H; pose proof (parity_of_correct_helper n) as H'.
  rewrite H in H'; assumption.
Qed.
Goal is_even 9002. vm_compute; do 10 constructor. Show Proof. Abort.
Check (two_plus_even 9000
   (two_plus_even 8998
      (two_plus_even 8996
         (two_plus_even 8994
            (two_plus_even 8992
               (two_plus_even 8990
                  (two_plus_even 8988
                     (two_plus_even 8986
                        (two_plus_even 8984 (two_plus_even 8982 ?[Goal])))))))))).
Goal is_even 9002. apply parity_of_correct; vm_compute; reflexivity. Qed.
