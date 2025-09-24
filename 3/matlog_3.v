Example problem_1 ( A B C : Prop )(x : A -> B) (y: B -> C) : A -> C.  
Proof.
intros z. 
apply y.
apply x.
exact z.
Show Proof.
Qed.

Example problem_1_2 : forall ( A B C : Prop ), (A -> B) -> (B -> C) -> ( A -> C).
Proof.
intros. 
apply H0.
apply H.
exact H1.
Show Proof.
Qed.

Example problem_2 : forall ( A B C : Prop ), ((A /\ B) -> C) -> ( A -> (B -> C)).
Proof. 
intros.
apply H.
split.
 - exact H0.
 - exact H1.
Show Proof. 
Qed.

Example HF_1 : forall ( A B C : Prop ), ( A -> (B -> C)) -> ((A /\ B) -> C).
Proof.
Abort.


Example problem_3 : forall ( A B C : Prop ), ((A -> C) /\ (B -> C)) -> ((A \/ B) -> C).
Proof. 
intros.
destruct H0.
 - destruct H as [K1 K2].
   apply K1.
   exact H0.
 - destruct H as [K1 K2].
   apply K2.
   exact H0.
Qed.

Example HF_2 : forall ( A B C : Prop ), ((A \/ B) -> C) -> ((A -> C) /\ (B -> C)).
Proof. 
Abort. 


