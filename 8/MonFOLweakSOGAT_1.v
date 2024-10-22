Parameter Invar : Set.

Inductive Fm : Set :=
  | Tru : Fm
  | Imp : Fm -> Fm -> Fm
  | Exi : Fm -> Fm
  | Uni : Fm -> Fm
  | Sub : Tm -> Fm -> Fm
with Tm : Set :=
  | InvarisTm : Invar -> Tm.

Parameter Pfvar : Fm -> Set.

Inductive Pf : Fm -> Set := 
 
  (*rules for propositional connectives*)
  | tt : Pf Tru
  | hyp : forall (A : Fm), (Pfvar A -> Pf A)
  | lam : forall (A B : Fm), (Pfvar A -> Pf B) -> Pf (Imp A B)
  | app : forall A B : Fm, Pf (Imp A B) -> Pf A -> Pf B
 
  (*rules for the existential quantifier*)
  | exii : forall (A : Fm) (t : Tm), Pf (Sub t A) -> Pf (Exi A)
  | exie : forall (A C : Fm), Pf (Exi A) -> (forall x : Invar, Pfvar (Sub (InvarisTm x) A) -> Pf C) -> Pf C

  (*rules for the universial quantifier*)
  | unii : forall (A : Fm), (forall x : Invar, Pf (Sub (InvarisTm x) A)) -> Pf (Uni A)
  | unie : forall (A : Fm), Pf (Uni A) -> (forall t : Tm, Pf (Sub t A))
  
  (*substitution is invariant with respect to the type formers*)
  | sub_imp_1 : forall (A B : Fm) (t : Tm), Pf (Sub t (Imp A B)) -> Pf (Imp (Sub t A) (Sub t B))
  | sub_imp_2 : forall (A B : Fm) (t : Tm), Pf (Imp (Sub t A) (Sub t B)) -> Pf (Sub t (Imp A B))
  
  (*Exi makes 0 variable formulas*)
  | sub_exi_1 : forall (A : Fm) (t : Tm), Pf (Sub t (Exi A)) -> Pf (Exi A)
  | sub_exi_2 : forall (A : Fm) (t : Tm), Pf (Exi A) -> Pf (Sub t (Exi A)). 

Infix "⊃" := Imp (at level 80, right associativity). 

Lemma prenex_1 : forall (A B : Fm), Pf (((Exi A) ⊃ (Exi B)) ⊃ (Uni (A ⊃ (Exi B)))).
Proof.
intros.
apply lam.
intros.
apply hyp in H.
apply unii.
intros.
apply sub_imp_2.
apply lam.
intros.
apply hyp in H0.
assert (K: Pf (Exi B) -> Pf (Sub (InvarisTm x) (Exi B)) ).
intros. 
apply sub_exi_2 with (t:=(InvarisTm x)) in H1.
auto.
apply K.
apply app with (A:=Exi A) (B:=(Exi B)).
auto.
apply exii with (t:=(InvarisTm x)).
auto.
Qed.

Lemma prenex_2 : forall (A B : Fm), Pf (((Exi A) ⊃ (Uni B)) ⊃ (Uni ((Exi A) ⊃ B))).
Proof.
intros.
apply lam.
intros.
apply hyp in H.
apply unii.
intros.
apply sub_imp_2.
apply lam.
intros.
apply hyp in H0.
apply sub_exi_1 in H0.
apply app with (B:=Uni B) in H0. 
apply unie with (t:=(InvarisTm x)) in H0.
all: auto.
Qed.