Inductive is_even : nat -> Prop :=
| zero_even : is_even 0
| two_plus_even {n} : is_even n -> is_even (S (S n)).
Inductive parity := even | odd.
Definition flip_parity p
  := match p with even => odd | odd => even end.
Fixpoint parity_of (n : nat) : parity :=
  match n with
  | O => even
  | S n' => flip_parity (parity_of n')
  end.
Lemma parity_of_correct : forall n, parity_of n = even -> is_even n.
Admitted.
Goal is_even 9002. apply parity_of_correct; vm_compute; reflexivity. Qed.
