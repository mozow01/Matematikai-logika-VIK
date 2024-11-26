Lemma log_1 : forall A B : Prop, A -> ((A -> B) -> B).
Proof.
firstorder.
Qed.

(*Continuation*)
Lemma log_2 : forall A B : Prop, ((A -> B) -> B) -> A.
Proof.
firstorder.
Abort.

(*Call/cc Peirce szabály*)
Lemma log_3 : forall A B : Prop, ((A -> B) -> A) -> A.
Proof.
firstorder.
Abort.

Lemma log_4 : forall A B : Prop, (A \/ (~ A)) -> ((A -> B) -> A) -> A.
Proof.
firstorder.
Qed.
