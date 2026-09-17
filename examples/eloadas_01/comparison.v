(* 5. példa: szintaxis, kiértékelés és denotáció összehasonlítása. *)

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

(* Nem ugyanaz a szintaxisfa. *)
Example kulonbozo_szintaxis :
  And Tru Tru <> And2 Tru Tru.
Proof.
  unfold And, And2.
  discriminate.
Qed.

(* Ugyanaz a kiértékelési eredmény. *)
Example azonos_redukalt_eredmeny :
  beta_reduce (And Tru Tru) = beta_reduce (And2 Tru Tru).
Proof.
  reflexivity.
Qed.

(* Ugyanaz a denotáció. *)
Example azonos_denotacio :
  denote (And Tru Tru) = denote (And2 Tru Tru).
Proof.
  reflexivity.
Qed.
