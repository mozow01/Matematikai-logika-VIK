(* 3. példa: a Boole-kifejezések denotációja a beépített bool típusban. *)

Inductive Boole : Type :=
| Tru : Boole
| Fal : Boole
| Ite : Boole -> Boole -> Boole -> Boole.

Definition And (A B : Boole) : Boole :=
  Ite A (Ite B Tru Fal) Fal.

Definition And2 (A B : Boole) : Boole :=
  Ite A B Fal.

Fixpoint denote (A : Boole) : bool :=
  match A with
  | Tru => true
  | Fal => false
  | Ite A B C =>
      if denote A then denote B else denote C
  end.

Compute denote Tru.
Compute denote (Ite Fal Tru Fal).
Compute denote (And Tru Fal).
Compute denote (And2 Tru Tru).

Example denotacios_pelda :
  denote (Ite (Ite Fal Fal Tru) Tru Fal) = true.
Proof.
  reflexivity.
Qed.

(* Két különböző definíció ugyanazt a jelentést adhatja. *)
Theorem And_denote_azonos :
  forall A B,
    denote (And2 A B) = denote (And A B).
Proof.
  intros A B.
  unfold And2, And.
  simpl.
  destruct (denote A), (denote B); reflexivity.
Qed.
