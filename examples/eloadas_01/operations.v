(* 2. példa: származtatott műveletek Ite segítségével. *)

Inductive Boole : Type :=
| Tru : Boole
| Fal : Boole
| Ite : Boole -> Boole -> Boole -> Boole.

Definition Neg (A : Boole) : Boole :=
  Ite A Fal Tru.

Definition And (A B : Boole) : Boole :=
  Ite A (Ite B Tru Fal) Fal.

Definition And2 (A B : Boole) : Boole :=
  Ite A B Fal.

Print Neg.
Print And.
Print And2.

(* Az unfold csak kibontja a megadott definíciót. *)
Example neg_kibontasa :
  Neg Fal = Ite Fal Fal Tru.
Proof.
  unfold Neg.
  reflexivity.
Qed.

Example and2_kibontasa :
  And2 Tru Fal = Ite Tru Fal Fal.
Proof.
  unfold And2.
  reflexivity.
Qed.
