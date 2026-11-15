Lemma diszjunkcio_bal : forall A B : Prop,
  A -> A \/ B.
Proof.
  intros A B HA.
  left.
  exact HA.
Qed.

Lemma diszjunkcio_jobb : forall A B : Prop,
  B -> A \/ B.
Proof.
  intros A B HB.
  right.
  exact HB.
Qed.

Lemma diszjunkcio_felcserel : forall A B : Prop,
  A \/ B -> B \/ A.
Proof.
  intros A B H.
  destruct H as [HA | HB].
  - right.
    exact HA.
  - left.
    exact HB.
Qed.

Lemma diszjunkcio_esetek : forall A B C : Prop,
  (A -> C) -> (B -> C) -> A \/ B -> C.
Proof.
  intros A B C HAC HBC H.
  destruct H as [HA | HB].
  - apply HAC.
    exact HA.
  - apply HBC.
    exact HB.
Qed.

Lemma ellentmondasbol_barmi : forall A : Prop,
  False -> A.
Proof.
  intros A H.
  destruct H.
Qed.

Lemma ellentmondo_feltevesek : forall A B : Prop,
  A -> ~ A -> B.
Proof.
  intros A B HA HnA.
  exfalso.
  apply HnA.
  exact HA.
Qed.

Lemma kettos_tagadas_bevezetese : forall A : Prop,
  A -> ~ ~ A.
Proof.
  intros A HA HnA.
  apply HnA.
  exact HA.
Qed.

Lemma tagado_kovetkeztetes : forall A B : Prop,
  (A -> B) -> ~ B -> ~ A.
Proof.
  intros A B HAB HnB HA.
  apply HnB.
  apply HAB.
  exact HA.
Qed.

Theorem de_morgan_vagy : forall A B : Prop,
  ~ (A \/ B) <-> (~ A /\ ~ B).
Proof.
  intros A B.
  split.
  - intro H.
    split.
    + intro HA.
      apply H.
      left.
      exact HA.
    + intro HB.
      apply H.
      right.
      exact HB.
  - intros H HAB.
    destruct H as [HnA HnB].
    destruct HAB as [HA | HB].
    + apply HnA.
      exact HA.
    + apply HnB.
      exact HB.
Qed.

Theorem de_morgan_es_eldontheto : forall A B : Prop,
  (A \/ ~ A) ->
  (~ (A /\ B) <-> (~ A \/ ~ B)).
Proof.
  intros A B DontesA.
  split.
  - intro H.
    destruct DontesA as [HA | HnA].
    + right.
      intro HB.
      apply H.
      split.
      * exact HA.
      * exact HB.
    + left.
      exact HnA.
  - intros Hn H.
    destruct Hn as [HnA | HnB].
    + apply HnA.
      destruct H as [HA HB].
      exact HA.
    + apply HnB.
      destruct H as [HA HB].
      exact HB.
Qed.

Theorem implikacio_jellemzese_eldontheto : forall A B : Prop,
  (A \/ ~ A) ->
  ((A -> B) <-> (~ A \/ B)).
Proof.
  intros A B DontesA.
  split.
  - intro HAB.
    destruct DontesA as [HA | HnA].
    + right.
      apply HAB.
      exact HA.
    + left.
      exact HnA.
  - intros H HA.
    destruct H as [HnA | HB].
    + exfalso.
      apply HnA.
      exact HA.
    + exact HB.
Qed.

Theorem kizartharmadik_kettos_tagadasa : forall A : Prop,
  ~ ~ (A \/ ~ A).
Proof.
  intros A H.
  apply H.
  right.
  intro HA.
  apply H.
  left.
  exact HA.
Qed.
