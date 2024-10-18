Require Import Lia.

Fixpoint összeg (n:nat) :=
match n with 
  | 0 => 0
  | S n => (összeg n) + S n
end.

Theorem első_n_szám_összege : forall n, 2*(összeg n) = n*(n+1).
Proof.
intros.
induction n.
simpl.
reflexivity.
simpl.
simpl in IHn.
lia.
Show Proof.
Qed.