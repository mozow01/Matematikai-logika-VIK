(*Prop a Coq-ban egy "sort":

Prop típus, amelynek lakói az állítások

Set típus, amelynek a lakói extraktálható programok 
 
  -- típusos
    -- polimorf: x: list string ; x: list A
    -- dependent p: 0=0 

Type (Coq)

 *)

Print and.

Search nat.

Print Nat.log2. 

Print or. 

Lemma problem_1 : forall A B : Prop, A -> B -> A /\ B.
Proof.
intros A B.
intro x.
intro y.
split.
exact x.
assumption.
Qed.

Print problem_1.

Lemma pr_2 : forall A B : Prop, A -> B -> A \/ B.
Proof.
intros.
left.
assumption.
Qed.

Lemma pr_3 : forall A B C : Prop,
(A /\ (B \/ C)) -> ((A /\ B) \/ (A /\ C)).
Proof.
intros.
destruct H as [H1 H2].
destruct H2 as [K|L].
left.
Show Proof.
auto.
Show Proof.
right.
auto.
Defined.

Compute (fun (A B C : Prop) (H : A /\ (B \/ C)) =>
match H with
| conj x x0 =>
    (fun (H1 : A) (H2 : B \/ C) =>
     match H2 with
     | or_introl x1 =>
         (fun K : B => or_introl (conj H1 K)) x1
     | or_intror x1 =>
         (fun L : C => or_intror (conj H1 L)) x1
     end) x x0
end).








