(* Gyakorlás 5/16: a diszjunkció denotációja. *)

Inductive Boole : Type :=
| Tru : Boole
| Fal : Boole
| Ite : Boole -> Boole -> Boole -> Boole.

Definition Neg (A : Boole) : Boole := Ite A Fal Tru.
Definition And (A B : Boole) : Boole := Ite A (Ite B Tru Fal) Fal.
Definition And2 (A B : Boole) : Boole := Ite A B Fal.

Fixpoint denote (A : Boole) : bool :=
  match A with
  | Tru => true
  | Fal => false
  | Ite A B C => if denote A then denote B else denote C
  end.

Fixpoint beta_reduce (A : Boole) : Boole :=
  match A with
  | Tru => Tru
  | Fal => Fal
  | Ite A B C =>
      match beta_reduce A with
      | Tru => beta_reduce B
      | Fal => beta_reduce C
      | A' => Ite A' B C
      end
  end.

(* Útmutatás: a denote A logikai értéke szerint bonts esetekre.
   Az Abort. helyére írd a taktikákat, majd zárd a bizonyítást Qed.-del. *)
Theorem ite_or_denote :
  forall A B,
    denote (Ite A Tru B) = orb (denote A) (denote B).
Proof.
  (* Ide kerül a bizonyítás. *)
Abort.
