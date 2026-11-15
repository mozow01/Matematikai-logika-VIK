Require Import Classical.

(* Az 1. feladat megoldása: 1-C, 2-A, 3-B. *)
Section Feladat1.

Variable U : Type.
Variables P Q : U -> Prop.

Lemma gy1_A :
  (exists x, P x) -> (exists x, Q x) \/ (exists x, P x).
Proof.
  intro H.
  right.
  exact H.
Qed.

Lemma gy1_B :
  (exists x, P x) -> (exists x, Q x) \/ (exists x, P x).
Proof.
  intro H.
  right.
  destruct H as [a Ha].
  exists a.
  exact Ha.
Qed.

Lemma gy1_C :
  (exists x, P x) -> (exists x, Q x) \/ (exists x, P x).
Proof.
  intro H.
  destruct H as [a Ha].
  right.
  exists a.
  exact Ha.
Qed.

End Feladat1.

(* A 2. feladat megoldása: az A program. *)
Section Feladat2.

Variable U : Type.
Variables P Q : U -> Prop.

Lemma gy2_A :
  ((forall x, P x) /\ (forall x, Q x)) ->
  (forall x, Q x) \/ (forall x, P x).
Proof.
  intro H.
  left.
  intro a.
  exact ((proj2 H) a).
Qed.

Lemma gy2_B :
  ((forall x, P x) /\ (forall x, Q x)) ->
  (forall x, Q x) \/ (forall x, P x).
Proof.
  intro H.
  left.
  exact (proj2 H).
Qed.

Lemma gy2_C :
  ((forall x, P x) /\ (forall x, Q x)) ->
  (forall x, Q x) \/ (forall x, P x).
Proof.
  intro H.
  right.
  intro a.
  exact ((proj1 H) a).
Qed.

End Feladat2.

Section Feladat3.

Variable U : Type.
Variable u0 : U.
Variables Atvizsgal CimketKap : U -> Prop.

Lemma feladat3_megoldas :
  ((forall x, Atvizsgal x) -> exists y, CimketKap y) <->
  exists x, (Atvizsgal x -> exists y, CimketKap y).
Proof.
  split.
  - intro H.
    destruct (classic (exists x, ~ Atvizsgal x)) as [[x Hx] | Hnincs].
    + exists x.
      intro Ax.
      contradiction.
    + exists u0.
      intro Au0.
      apply H.
      intro x.
      apply NNPP.
      intro Hx.
      apply Hnincs.
      exists x.
      exact Hx.
  - intros [x Hx] Hall.
    apply Hx.
    apply Hall.
Qed.

End Feladat3.

Section Feladat4.

Variable U : Type.
Variables Beadta Visszajelzes : U -> Prop.

Lemma feladat4_megoldas :
  ~ (forall x, Beadta x -> Visszajelzes x) <->
  exists x, Beadta x /\ ~ Visszajelzes x.
Proof.
  split.
  - intro H.
    destruct (classic (exists x, Beadta x /\ ~ Visszajelzes x))
      as [Hex | Hnincs].
    + exact Hex.
    + exfalso.
      apply H.
      intros x Bx.
      apply NNPP.
      intro HnV.
      apply Hnincs.
      exists x.
      split.
      * exact Bx.
      * exact HnV.
  - intros [x [Bx HnV]] Hall.
    apply HnV.
    apply Hall.
    exact Bx.
Qed.

End Feladat4.
