(* Gyakorlás 1/16: háromszintű béta-redukció (Tru/Tru/Tru). *)

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

(* Feladat: kövesd belülről kifelé, melyik ágakat választjuk.
   Az Abort. helyére írd a taktikákat, majd zárd a bizonyítást Qed.-del. *)
Theorem beta_nested_ttt :
  forall A B C D E F G,
    beta_reduce A = Tru ->
    beta_reduce B = Tru ->
    beta_reduce D = Tru ->
    beta_reduce (Ite (Ite (Ite A B C) D E) F G) = beta_reduce F.
Proof.
  (* Ide kerül a bizonyítás. *)
Abort.
