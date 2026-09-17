(* Gyakorlás 15/16: beágyazott állandó hamis. *)

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

(* Útmutatás: válaszd külön a szintaktikai nem-egyenlőséget és a denotációs
   egyenlőséget. Az Abort. helyére írd a taktikákat, majd használj Qed.-et. *)
Theorem nested_false_branches :
  forall A B,
    Ite A (Ite B Fal Fal) Fal <> Fal /\
    denote (Ite A (Ite B Fal Fal) Fal) = denote Fal.
Proof.
  (* Ide kerül a bizonyítás. *)
Abort.
