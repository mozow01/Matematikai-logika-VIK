Lemma minden_specializalas : forall (U : Type) (P : U -> Prop) (t : U),
  (forall x, P x) -> P t.
Proof.
  intros U P t H.
  apply H.
Qed.

Lemma minden_pontonként : forall (U : Type) (P Q : U -> Prop),
  (forall x, P x -> Q x) ->
  (forall x, P x) ->
  forall x, Q x.
Proof.
  intros U P Q HPQ HP x.
  apply HPQ.
  apply HP.
Qed.

Lemma minden_felcserel : forall (U V : Type) (R : U -> V -> Prop),
  (forall x, forall y, R x y) ->
  forall y, forall x, R x y.
Proof.
  intros U V R H y x.
  apply H.
Qed.

Lemma letezik_bevezetes : forall (U : Type) (P : U -> Prop) (t : U),
  P t -> exists x, P x.
Proof.
  intros U P t HP.
  exists t.
  exact HP.
Qed.

Lemma letezik_kep : forall (U : Type) (P Q : U -> Prop),
  (forall x, P x -> Q x) ->
  (exists x, P x) ->
  exists x, Q x.
Proof.
  intros U P Q HPQ HP.
  destruct HP as [x HPx].
  exists x.
  apply HPQ.
  exact HPx.
Qed.

Lemma letezik_kozos_kovetkezmeny : forall (U : Type) (P : U -> Prop) (Q : Prop),
  (forall x, P x -> Q) ->
  (exists x, P x) ->
  Q.
Proof.
  intros U P Q H HP.
  destruct HP as [x HPx].
  apply H with (x := x).
  exact HPx.
Qed.

Lemma letezik_konjunkcio_bal : forall (U : Type) (P Q : U -> Prop),
  (exists x, P x /\ Q x) ->
  exists x, P x.
Proof.
  intros U P Q H.
  destruct H as [x [HPx HQx]].
  exists x.
  exact HPx.
Qed.

Lemma letezik_konjunkcio_jobb : forall (U : Type) (P Q : U -> Prop),
  (exists x, P x /\ Q x) ->
  exists x, Q x.
Proof.
  intros U P Q H.
  destruct H as [x [HPx HQx]].
  exists x.
  exact HQx.
Qed.

Lemma minden_konjunkcio : forall (U : Type) (P Q : U -> Prop),
  (forall x, P x /\ Q x) ->
  (forall x, P x) /\ (forall x, Q x).
Proof.
  intros U P Q H.
  split.
  - intro x.
    destruct (H x) as [HPx HQx].
    exact HPx.
  - intro x.
    destruct (H x) as [HPx HQx].
    exact HQx.
Qed.

Theorem egy_tanu_mindenre : forall (U V : Type) (R : U -> V -> Prop),
  (exists x, forall y, R x y) ->
  forall y, exists x, R x y.
Proof.
  intros U V R H y.
  destruct H as [x Hx].
  exists x.
  apply Hx.
Qed.

Theorem letezik_vagy_szetszedes : forall (U : Type) (P Q : U -> Prop),
  (exists x, P x \/ Q x) ->
  (exists x, P x) \/ (exists x, Q x).
Proof.
  intros U P Q H.
  destruct H as [x [HPx | HQx]].
  - left.
    exists x.
    exact HPx.
  - right.
    exists x.
    exact HQx.
Qed.
