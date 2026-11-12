(*
Prenex normál forma

(Q1 x1)(Q2 x2)(Q3 x3) B(x1,x2,...,xn)

(B -> (∀x, A x)) <-> ∀x,(B -> A x)
(B -> (∃x, A x)) <-> ∃x,(B -> A x)

((∀x, A x) -> B) <-> ∃x,(A x -> B)
((∃x, A x) -> B) <-> ∀x,(A x -> B)

Drinker Paradox:

(∃x,(∃x, A x) -> B)

Dual Drinker Paradox:

(∃x, B -> (∀x, A x))

*)

Lemma problem_1 : forall (U : Set) (A : U -> Prop) (B : Prop), (B -> (forall x, A x)) -> forall x,(B -> A x).
Proof. 
intros. 
apply H.
apply H0.
Defined.

Lemma problem_2 : forall (U : Set) (A : U -> Prop) (B : Prop),  (forall x,(B -> A x)) -> (B -> (forall x, A x)).
Proof. 
intros. 
apply H.
apply H0.
Defined.

Lemma problem_3 : forall (U : Set) (A : U -> Prop) (B : Prop), (exists (x : U), True) -> ((forall x, A x) \/ exists x, ~ A x) -> ((forall x, A x) -> B) -> exists x,(A x -> B).
Proof. 
intros. 
elim H0.
intros.
 - intros.
   elim H.
   intros.
   exists x.
   intros.
   apply H1.
   intros.
   apply H2.
 - intros.
   elim H2. 
   intros.
   exists x.
   intros.
   contradiction.
Defined.

Lemma problem_4 : forall (U : Set) (A : U -> Prop) (B : Prop), (exists (x : U), True) -> ((forall x, A x) \/ exists x, ~ A x) -> (exists x,(A x -> B)) -> ((forall x, A x) -> B).
Proof. 
intros.
elim H0.
 - intros.
   elim H.
   intros.
   elim H1.
   intros.
   apply H5.
   apply H2.
 - intros.
   elim H1. elim H. elim H3.
   intros.
   apply H6.
   apply H2.
Defined.

Lemma problem_5 : forall (U : Type) (A : U -> Prop), (exists (x : U), True) -> ((exists x, A x) \/ ~ (exists x, A x)) -> (exists x, (exists x, A x) -> A x).
Proof.
intros.
elim H0.
intros.
 - elim H1.
   intros.
   exists x.
   intros.
   exact H2.
   
   
   


   
