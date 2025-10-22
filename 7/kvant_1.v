Lemma problem_1 (U : Type) (A : U -> U -> Prop) : (exists x, forall y, A x y ) -> (forall y, exists x,  A x y ).
Proof. 
intros.
elim H.
intros.
exists x. 
apply H0.
Qed.

Lemma problem_2 (U : Type) (P Q : U -> Prop) : (forall x, P x /\ Q x ) -> (forall x, P x) /\ (forall x, Q x).
Proof.
intros.
split.
 - intros.
   assert (K: P x /\ Q x).
   apply H.
   destruct K.
   exact H0.
- intros.
  firstorder.
Qed.

(* 

Bárki felszólal, valaki megsértődik. 
Tehát mindenkire igaz az, hogy valaki megsértődik, ha ő felszólal.

(exists x, F x) -> exists y, M y



*)

Lemma problem_3_0 (U : Type) (F : U -> Prop) : ~ (exists x, F x) -> (forall x, ~ F x).
Proof.
firstorder.
Qed. 

Lemma problem_3 (U : Type) (F M : U -> Prop) : ((exists x, F x) \/ ~ (exists x, F x)) -> ((exists x, F x) -> (exists x, M x)) -> (forall x, F x -> (exists x, M x)).
Proof. 
intros.
destruct H.
apply H0 in H. 
exact H.
apply problem_3_0 with (x:=x) in H.
contradiction.
Qed. 

(*

(forall x, F x -> (exists x, M x)) -> (forall x, exists y, F x -> M y)

(forall x, exists y, F x -> M y) prenex normálforma

*)

 
