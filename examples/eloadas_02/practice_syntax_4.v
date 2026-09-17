(* Gyakorlás 16/16: beágyazott konjunkció és állandó hamis. *)

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

(* Útmutatás: az And2 kibontása után a bal oldal szintaktikája, illetve
   denotációja külön kezelhető. Az Abort. helyére írd a taktikákat, majd
   használj Qed.-et. *)
Theorem nested_and_false :
  forall A B,
    And2 A (And2 B Fal) <> Fal /\
    denote (And2 A (And2 B Fal)) = denote Fal.
Proof.
  (* Ide kerül a bizonyítás. *)
Abort.
