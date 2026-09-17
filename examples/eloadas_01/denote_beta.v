(* 7. példa: a beta-redukció megőrzi a denotációt. *)

Inductive Boole : Type :=
| Tru : Boole
| Fal : Boole
| Ite : Boole -> Boole -> Boole -> Boole.

Fixpoint denote (A : Boole) : bool :=
  match A with
  | Tru => true
  | Fal => false
  | Ite A B C =>
      if denote A then denote B else denote C
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

Theorem denote_beta :
  forall A : Boole,
    denote (beta_reduce A) = denote A.
Proof.
  (* A felépítése szerinti indukció. *)
  induction A.
  (* A = Tru és A = Fal közvetlen számítás. *)
  - reflexivity.
  - reflexivity.
  (* A = Ite A1 A2 A3. *)
  - simpl.
    (* Megnézzük, mire redukálódik a feltétel. *)
    destruct (beta_reduce A1) eqn:H.
    + simpl in IHA1.
      rewrite <- IHA1.
      simpl.
      exact IHA2.
    + simpl in IHA1.
      rewrite <- IHA1.
      simpl.
      exact IHA3.
    + simpl in IHA1.
      simpl.
      rewrite IHA1.
      reflexivity.
Qed.
