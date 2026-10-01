Lemma problem_1 : forall A B : Prop, ((~ A) \/ B) -> (A -> B).
Proof.
intros A B H.
intros K.
destruct H as [H1 | H2]. 
 - contradiction.
   (* unfold not in H1.
   apply False_ind.
   apply H1.
   exact K. *)
 - exact H2.
Qed. 

(* A -> B -> C = A /\ B -> C Currying *)

Lemma problem_2 : forall A B : Prop,((~ A) \/ A) -> (A -> B) -> ((~ A) \/ B).
Proof.
intros.
destruct H.
 - left.
   auto.
 - right.
   apply H0.
   exact H.
Show Proof.
Qed.

Lemma problem_3 : forall A B : Prop, (A -> B) -> ((~ B) -> (~ A)).
Proof.
intros.
unfold not.
intros.
unfold not in H0.
apply H0.
apply H.
apply H1.
Qed.

Lemma problem_4 : forall A B : Prop, ((~ B) \/ B) -> ((~ B) -> (~ A)) -> (A -> B).
Proof.
intros.
destruct H.
assert (K : ~ A).
auto.
contradiction.
auto.
Qed.

Lemma problem_5 : forall A B C : Prop, A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
Proof.
intros.
destruct H.
destruct H0 as [H01 | H02].
left.
auto.
auto.
Qed.

(* HF Igazolja!*)

Lemma problem_6 : forall A B C : Prop, (A /\ B) \/ (A /\ C) -> A /\ (B \/ C).
Proof.
Abort. 

(* HF Ellenőrizze, hogy levezethető-e a konstruktív logikában és ha nem, akkor igazolja egy plusz feltétel "a kizárt harmadik elve" egy esetének hozzávételével!*)

Lemma problem_7 : forall A B C : Prop, ~ (A \/ B) -> ~ A /\ ~ B.
Proof.
Abort.

Lemma problem_8 : forall A B C : Prop, ~ (A /\ B) -> ~ A \/ ~ B.
Proof.
Abort.