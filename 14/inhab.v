Lemma example_1 : forall A B, (((A-> B)->B )->A)-> ((A -> B) -> A) -> A.
Proof.
intros.
apply X.
intros.
apply X1.
apply X0.
assumption.
Qed.

Lemma example_2 : forall A B C, (((A-> C)->C )->A)-> ((A -> C) -> (B->C)) -> B -> A.
Proof.
intros.
apply X.
intros.
apply X0.
assumption.
assumption.
Qed.

Lemma example_3 : forall A C, ((A-> C)->C )->A.
Proof.
intros.
Abort.

Lemma example_4 : forall A C, ((A-> C)->A )->A.
Proof.
intros.
apply X.
intros.
Abort.
