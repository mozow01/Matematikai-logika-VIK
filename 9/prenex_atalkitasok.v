(*
  A negy alapveto, implikaciora vonatkozo prenex atalakitasi szabaly.

  B nem fugg x-tol. Ezt a tipusa fejezi ki: B : Prop,
  mig A : U -> Prop.

  Nem hasznalunk klasszikus Coq-konyvtarat. Ahol dontesi vagy
  nemuressegi feltetel kell, az a tetel bemenetekent szerepel.
*)

Theorem prenex_forall_jobbra :
  forall (U : Type) (A : U -> Prop) (B : Prop),
    (B -> forall x, A x) <-> forall x, B -> A x.
Proof.
  intros U A B.
  split.
  - intros H x HB.
    apply H.
    exact HB.
  - intros H HB x.
    apply H with (x := x).
    exact HB.
Qed.

Theorem prenex_exists_balra :
  forall (U : Type) (A : U -> Prop) (B : Prop),
    ((exists x, A x) -> B) <-> forall x, A x -> B.
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

Theorem prenex_exists_jobbra :
  forall (U : Type) (A : U -> Prop) (B : Prop),
    (exists x : U, True) ->
    (B \/ ~ B) ->
    (B -> exists x, A x) <-> exists x, B -> A x.
Proof.
  intros U A B NemUres DonthetoB.
  split.
  - intro H.
    destruct DonthetoB as [HB | HnB].
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

Theorem prenex_forall_balra :
  forall (U : Type) (A : U -> Prop) (B : Prop),
    (exists x : U, True) ->
    ((forall x, A x) \/ exists x, ~ A x) ->
    ((forall x, A x) -> B) <-> exists x, A x -> B.
Proof.
  intros U A B NemUres DonthetoMinden.
  split.
  - intro H.
    destruct DonthetoMinden as [Hall | Hellenpelda].
    + destruct NemUres as [x Igaz].
      exists x.
      intro HAx.
      apply H.
      exact Hall.
    + destruct Hellenpelda as [x HnAx].
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
