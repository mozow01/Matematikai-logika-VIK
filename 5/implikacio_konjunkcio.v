Lemma implikacio_azonossag : forall A : Prop, A -> A.
Proof.
  intros A HA.
  exact HA.
Qed.

Lemma implikacio_elso : forall A B : Prop, A -> B -> A.
Proof.
  intros A B HA HB.
  exact HA.
Qed.

Lemma implikacio_lanc : forall A B C : Prop,
  (A -> B) -> (B -> C) -> A -> C.
Proof.
  intros A B C HAB HBC HA.
  apply HBC.
  apply HAB.
  exact HA.
Qed.

Lemma implikacio_felcserel : forall A B C : Prop,
  (A -> B -> C) -> B -> A -> C.
Proof.
  intros A B C H HB HA.
  apply H.
  - exact HA.
  - exact HB.
Qed.

Lemma konjunkcio_bevezetes : forall A B : Prop,
  A -> B -> A /\ B.
Proof.
  intros A B HA HB.
  split.
  - exact HA.
  - exact HB.
Qed.

Lemma konjunkcio_bal : forall A B : Prop,
  A /\ B -> A.
Proof.
  intros A B H.
  destruct H as [HA HB].
  exact HA.
Qed.

Lemma konjunkcio_jobb : forall A B : Prop,
  A /\ B -> B.
Proof.
  intros A B H.
  destruct H as [HA HB].
  exact HB.
Qed.

Lemma konjunkcio_felcserel : forall A B : Prop,
  A /\ B -> B /\ A.
Proof.
  intros A B H.
  destruct H as [HA HB].
  split.
  - exact HB.
  - exact HA.
Qed.

Lemma konjunkcio_atzarojel : forall A B C : Prop,
  A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
  intros A B C H.
  destruct H as [HA [HB HC]].
  split.
  - split.
    + exact HA.
    + exact HB.
  - exact HC.
Qed.

Theorem parbol_kulon : forall A B C : Prop,
  ((A /\ B) -> C) -> A -> B -> C.
Proof.
  intros A B C H HA HB.
  apply H.
  split.
  - exact HA.
  - exact HB.
Qed.

Theorem kulonbol_par : forall A B C : Prop,
  (A -> B -> C) -> (A /\ B) -> C.
Proof.
  intros A B C H HAB.
  destruct HAB as [HA HB].
  apply H.
  - exact HA.
  - exact HB.
Qed.

Theorem kozos_bemenet : forall A B C : Prop,
  (A -> B) /\ (A -> C) -> A -> B /\ C.
Proof.
  intros A B C H HA.
  destruct H as [HAB HAC].
  split.
  - apply HAB.
    exact HA.
  - apply HAC.
    exact HA.
Qed.
