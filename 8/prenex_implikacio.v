Lemma nem_letezik_akkor_mindenre_nem :
  forall (U : Type) (A : U -> Prop),
    (~ exists x, A x) -> forall x, ~ A x.
Proof.
  intros U A H x HAx.
  apply H.
  exists x.
  exact HAx.
Qed.

Lemma mindenre_nem_akkor_nem_letezik :
  forall (U : Type) (A : U -> Prop),
    (forall x, ~ A x) -> ~ exists x, A x.
Proof.
  intros U A H Hex.
  destruct Hex as [x HAx].
  apply H with (x := x).
  exact HAx.
Qed.

Theorem nem_letezik_azonossag :
  forall (U : Type) (A : U -> Prop),
    (~ exists x, A x) <-> forall x, ~ A x.
Proof.
  intros U A.
  split.
  - apply nem_letezik_akkor_mindenre_nem.
  - apply mindenre_nem_akkor_nem_letezik.
Qed.

Lemma letezik_ellenpelda_akkor_nem_minden :
  forall (U : Type) (A : U -> Prop),
    (exists x, ~ A x) -> ~ forall x, A x.
Proof.
  intros U A H Hall.
  destruct H as [x HnAx].
  apply HnAx.
  apply Hall.
Qed.

Theorem egy_tanu_mindenre :
  forall (U V : Type) (R : U -> V -> Prop),
    (exists x, forall y, R x y) ->
    forall y, exists x, R x y.
Proof.
  intros U V R H y.
  destruct H as [x Hx].
  exists x.
  apply Hx.
Qed.

Theorem prenex_minden_jobbra :
  forall (U : Type) (A : U -> Prop) (B : Prop),
    ((B -> forall x, A x) <-> forall x, B -> A x).
Proof.
  intros U A B.
  split.
  - intros H x HB.
    exact ((H HB) x).
  - intros H HB x.
    apply H.
    exact HB.
Qed.

Theorem prenex_letezik_balra :
  forall (U : Type) (A : U -> Prop) (B : Prop),
    (((exists x, A x) -> B) <-> forall x, A x -> B).
Proof.
  intros U A B.
  split.
  - intros H x HAx.
    apply H.
    exists x.
    exact HAx.
  - intros H Hex.
    destruct Hex as [x HAx].
    apply H with (x := x).
    exact HAx.
Qed.

Theorem prenex_letezik_jobbra :
  forall (U : Type) (A : U -> Prop) (B : Prop),
    (exists x : U, True) ->
    (B \/ ~ B) ->
    ((B -> exists x, A x) <-> exists x, B -> A x).
Proof.
  intros U A B NemUres DontesB.
  split.
  - intro H.
    destruct DontesB as [HB | HnB].
    + destruct (H HB) as [x HAx].
      exists x.
      intro HB2.
      exact HAx.
    + destruct NemUres as [x Igaz].
      exists x.
      intro HB.
      exfalso.
      apply HnB.
      exact HB.
  - intros H HB.
    destruct H as [x Hx].
    exists x.
    apply Hx.
    exact HB.
Qed.

Theorem prenex_minden_balra :
  forall (U : Type) (A : U -> Prop) (B : Prop),
    (exists x : U, True) ->
    ((forall x, A x) \/ exists x, ~ A x) ->
    (((forall x, A x) -> B) <-> exists x, A x -> B).
Proof.
  intros U A B NemUres DontesA.
  split.
  - intro H.
    destruct DontesA as [Hall | Hellen].
    + destruct NemUres as [x Igaz].
      exists x.
      intro HAx.
      apply H.
      exact Hall.
    + destruct Hellen as [x HnAx].
      exists x.
      intro HAx.
      exfalso.
      apply HnAx.
      exact HAx.
  - intros H Hall.
    destruct H as [x Hx].
    apply Hx.
    apply Hall.
Qed.
