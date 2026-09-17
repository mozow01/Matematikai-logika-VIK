(* 6. példa: minden Boole-kifejezés kiértékelése normálformára jut. *)

Inductive Boole : Type :=
| Tru : Boole
| Fal : Boole
| Ite : Boole -> Boole -> Boole -> Boole.

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

Definition is_normal (A : Boole) : Prop :=
  A = Tru \/ A = Fal.

Theorem weak_normalization :
  forall A : Boole,
    is_normal (beta_reduce A).
Proof.
  (* A felépítése szerinti indukció. *)
  induction A.
  (* A = Tru. *)
  - unfold is_normal.
    left.
    reflexivity.
  (* A = Fal. *)
  - unfold is_normal.
    right.
    reflexivity.
  (* A = Ite A1 A2 A3. *)
  - simpl.
    (* Az indukciós feltevés szerint a feltétel Tru vagy Fal lesz. *)
    destruct IHA1.
    + rewrite H.
      exact IHA2.
    + rewrite H.
      exact IHA3.
Qed.
