Theorem problem_2 : forall A B C : Prop, (A -> B) -> (B -> C) -> (A -> C).
Proof.
intros.
apply H0.
apply H.
apply H1.
Show Proof.
Qed.

Theorem problem_2_2 : forall A B C : Prop, (A -> B) -> (B -> C) -> (A -> C).
Proof.
firstorder.
Show Proof.
Eval simpl in (fun (A B C : Prop) (H : A -> B)(H0 : B -> C) (H1 : A) => (fun H2 : B =>(fun H3 : C => H3) (H0 H2)) (H H1)).
Qed.

Theorem problem_1 : forall A B C : Prop, (A -> B) -> (~ A \/ B).
Proof.
firstorder.
Abort.

Theorem problem_1_2 : forall A B C : Prop, (~ A \/ A) -> (A -> B) -> (~ A \/ B).
Proof.
intros.
destruct H.
- auto.
- auto.
Qed.

Theorem problem_3 : forall A B: Prop, ((A -> B) -> A) -> A.
Proof.
firstorder.
Abort.

Theorem problem_3_1 : forall A B: Prop, (~ A \/ A) -> 
((A -> B) -> A) -> A.
Proof.
firstorder.
Qed.

Theorem problem_4 : forall A B: Prop, ((A -> B) /\ B) -> A.
Proof.
firstorder.
Abort.
