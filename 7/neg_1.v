Lemma ch_1 : forall A B C : Prop, (A -> B) -> (B -> C) -> A -> C.
Proof. 
intros.
apply H0.
apply H.
exact H1.
Show Proof.
Qed.

Eval simpl in (fun (A B C : Prop) (H : A -> B)
   (H0 : B -> C) (H1 : A) =>
 H0 (H H1)).

Lemma kontrapoz_2 : forall A B : Prop, (A -> B) -> (~ B) -> (~ A).
Proof.
intros.
unfold not in *.
intro.
apply H0.
apply H.
exact H1.
Show Proof.
Qed.

(*
Lemma LEM : forall A : Prop, (A \/ ~A).
Proof.
firstorder.
*)

Lemma Peirce : forall A B : Prop, (A \/ ~A) -> ((A -> B) -> A) -> A.
Proof.
firstorder.
Qed.

Lemma kontrapoz_1 : forall A B : Prop, (A \/ ~A) -> ((~ A) -> (~ B)) -> B -> A.
Proof.
intros.
unfold not in *.
destruct H as [K1|K2].
 - auto.
 - apply False_ind.
   apply H0.
   exact K2.
   exact H1.
Show Proof. 
Qed.

Eval simpl in (fun (A B : Prop) (H : A \/ ~ A)
   (H0 : ~ A -> ~ B) (H1 : B) =>
 match H with
 | or_introl x =>
     (fun K1 : A => K1) x
 | or_intror x =>
     (fun K2 : A -> False =>
      False_ind A (H0 K2 H1)) x
 end).

Lemma DM_1 : forall A B : Prop, ((~ A) \/ (~ B)) -> ~ (A /\ B).
Proof.
intros.
unfold not in *.
destruct H as [K1|K2].
 - intros.
   apply K1.
   destruct H as (H1,H2).
   assumption.
 - intros.
   apply K2.
   destruct H as (H1,H2).
   assumption.
Show Proof. 
Qed.

Lemma DM_2 : forall A B : Prop,  ~ (A /\ B) -> ((~ A) \/ (~ B)).
Proof.
