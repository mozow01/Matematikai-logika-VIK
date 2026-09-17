(* 4. példa: a Boole-kifejezések kiértékelése. *)

Inductive Boole : Type :=
| Tru : Boole
| Fal : Boole
| Ite : Boole -> Boole -> Boole -> Boole.

Definition Neg (A : Boole) : Boole :=
  Ite A Fal Tru.

Definition And2 (A B : Boole) : Boole :=
  Ite A B Fal.

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

Compute beta_reduce (Ite Tru Fal Tru).
Compute beta_reduce (Ite (Ite Fal Fal Tru) Tru Fal).
Compute beta_reduce (And2 (Neg Fal) (Neg Tru)).

Example redukcios_pelda :
  beta_reduce
    (Ite (And2 Tru (Neg Tru))
         (Neg Fal)
         (And2 (Neg Fal) Tru)) = Tru.
Proof.
  reflexivity.
Qed.
