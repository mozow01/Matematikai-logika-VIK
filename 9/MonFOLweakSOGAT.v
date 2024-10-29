Parameter Invar : Set.

Inductive Fm : Set :=
  | Tru : Fm
  | Fls : Fm
  | Imp : Fm -> Fm -> Fm
  | Cnj : Fm -> Fm -> Fm
  | Dis : Fm -> Fm -> Fm
  | Exi : Fm -> Fm
  | Uni : Fm -> Fm
  | Sub : Tm -> Fm -> Fm
with Tm : Set :=
  | InvarisTm : Invar -> Tm.

Parameter Pfvar : Fm -> Set.

Inductive Pf : Fm -> Set := 
 
  (*rules for propositional connectives*)

  (*truth*)
  | tt : Pf Tru
  | hyp : forall (A : Fm), (Pfvar A -> Pf A)
  
  (*false*)
  | exfalso : forall (A : Fm), (Pf Fls -> Pf A)
  

  (*implication*)
  | lam : forall (A B : Fm), (Pfvar A -> Pf B) -> Pf (Imp A B)
  | app : forall A B : Fm, (Pf (Imp A B)) -> Pf A -> Pf B
 
  (*conjunction*)
  | cnji : forall (A B : Fm), Pf A -> Pf B -> Pf (Cnj A B)
  | cnjel : forall A B : Fm, Pf (Cnj A B) -> Pf A
  | cnjer : forall A B : Fm, Pf (Cnj A B) -> Pf B

  (*disjunction*)
  | disil : forall A B : Fm, Pf A -> Pf (Dis A B)
  | disir : forall A B : Fm, Pf B -> Pf (Dis A B) 
  | dise : forall (A B C : Fm), Pf (Dis A B) -> (Pfvar A -> Pf C) -> (Pfvar B -> Pf C)-> Pf C

  (*rules for the existential quantifier*)
  | exii : forall (A : Fm) (t : Tm), Pf (Sub t A) -> Pf (Exi A)
  | exie : forall (A C : Fm), Pf (Exi A) -> (forall x : Invar, Pfvar (Sub (InvarisTm x) A) -> Pf C) -> Pf C

  (*rules for the universial quantifier*)
  | unii : forall (A : Fm), (forall x : Invar, Pf (Sub (InvarisTm x) A)) -> Pf (Uni A)
  | unie : forall (A : Fm), Pf (Uni A) -> (forall t : Tm, Pf (Sub t A))
  
  (*substitution is invariant with respect to the type formers*)
  | sub_imp_1 : forall (A B : Fm) (t : Tm), Pf (Sub t (Imp A B)) -> Pf (Imp (Sub t A) (Sub t B))
  | sub_imp_2 : forall (A B : Fm) (t : Tm), Pf (Imp (Sub t A) (Sub t B)) -> Pf (Sub t (Imp A B))

  | sub_cnj_1 : forall (A B : Fm) (t : Tm), Pf (Sub t (Cnj A B)) -> Pf (Cnj (Sub t A) (Sub t B))
  | sub_cnj_2 : forall (A B : Fm) (t : Tm), Pf (Cnj (Sub t A) (Sub t B)) -> Pf (Sub t (Cnj A B))

  | sub_dis_1 : forall (A B : Fm) (t : Tm), Pf (Sub t (Dis A B)) -> Pf (Dis (Sub t A) (Sub t B))
  | sub_dis_2 : forall (A B : Fm) (t : Tm), Pf (Dis (Sub t A) (Sub t B)) -> Pf (Sub t (Dis A B))

  (*Exi makes 0 variable formulas*)
  | sub_exi_1 : forall (A : Fm) (t : Tm), Pf (Sub t (Exi A)) -> Pf (Exi A)
  | sub_exi_2 : forall (A : Fm) (t : Tm), Pf (Exi A) -> Pf (Sub t (Exi A))

  (*Uni makes 0 variable formulas*)
  | sub_uni_1 : forall (A : Fm) (t : Tm), Pf (Sub t (Uni A)) -> Pf (Uni A)
  | sub_uni_2 : forall (A : Fm) (t : Tm), Pf (Uni A) -> Pf (Sub t (Uni A)). 

Infix "⊃" := Imp (at level 80, right associativity). 
Infix "∧" := Cnj (at level 80, right associativity).
Infix "∨" := Dis (at level 80, right associativity). 

Notation "⊤" := Tru (at level 80, no associativity). 
Notation "⊥" := Fls (at level 80, no associativity). 
Notation "∃" := Exi (at level 80, no associativity). 
Notation "∀" := Uni (at level 80, no associativity). 


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

Lemma prenex_3 : forall (A B : Fm), Pf (Dis (Exi A) ((Exi A) ⊃ Fls)) -> Pf (((Exi A) ⊃ (Exi B)) ⊃ (Uni (A ⊃ (Exi B)))).
Proof.
intros.
apply lam.
intros.
apply hyp in H0.
apply unii.
intros.
apply sub_imp_2.
apply lam.
intros.
apply hyp in H1.
apply dise with (C:=Sub (InvarisTm x) ((∃) B)) in H.
apply H.
intros.
apply hyp in H2.
apply sub_exi_2.
exact (app ((∃) A) ((∃) B) H0 H2).
intros.
apply sub_exi_2.
apply hyp in H2.
apply exii in H1.
assert (H3 : Pf Fls). 
exact (app ((∃) A) Fls H2 H1).
apply exfalso.
exact H3. 
Qed.

(*Kategorikus szemantika*)

Class Category := cat_mk {
  uHom := Type : Type;
  Obj : Type;
  Hom : Obj -> Obj -> uHom; 
  Id : forall x, Hom x x; 
  Compose : forall {x y z}, (Hom y z)->(Hom x y)->(Hom x z); 

  (* associativity, identity*)
  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
        (Compose f (Compose g h) ) = (Compose (Compose f g) h);
  id_1 : forall x y (f : (Hom x y)), (Compose f (Id x)) = f;
  id_2 : forall x y (f : (Hom x y)), (Compose (Id y) f) = f;
}.

Notation "x → y" := (Hom x y) (at level 90, right associativity) :
type_scope.

Notation "f ∘ g" := (Compose f g) (at level 40, left associativity) :
type_scope.

Definition Obj_Mon := Fm.

Definition Hom_Mon (A B : Obj_Mon) := Pf (Imp A B).

Lemma Id_lemma : forall A, Pf (Imp A A).
Proof.
intros.
apply lam.
intros x.
apply hyp.
exact x.
Show Proof.
Defined.

Definition Id_Mon (A : Obj_Mon) := lam A A (fun x : Pfvar A => hyp A x).

Lemma Compose_lemma : forall A B C, Pf (Imp A B) -> Pf (Imp B C) -> Pf (Imp A C).
Proof.
intros.
apply lam.
intros x.
apply app with (A:=B).
auto.
apply app with (A:=A).
auto.
apply hyp.
auto.
Show Proof.
Defined.

Definition Compose_Mon {A B C : Obj_Mon} (f : Hom_Mon B C) (g : Hom_Mon A B) := (lam A C (fun x : Pfvar A => app B C f (app A B g (hyp A x)))).

Axiom ProofIrrelevance : forall (A : Fm) (x y : Pf A), x = y.

Lemma id_1_Mon : forall A B (f : (Hom_Mon A B)), Compose_Mon f (Id_Mon A) = f.
Proof.
intros.
unfold Compose_Mon, Id_Mon.
apply ProofIrrelevance with (A:=Imp A B).
Defined.

Lemma id_2_Mon : forall A B (f : (Hom_Mon A B)), Compose_Mon (Id_Mon B) f = f.
Proof.
intros.
apply ProofIrrelevance with (A:=Imp A B).
Defined.

Lemma assoc_Mon : forall A B C D (f : Hom_Mon C D) (g : Hom_Mon B C) (h : Hom_Mon A B) , (Compose_Mon f (Compose_Mon g h)) = (Compose_Mon (Compose_Mon f g) h).
Proof.
intros.
apply ProofIrrelevance with (A:=Imp A D).
Defined.


Instance Mon_is_a_Cat : Category. 
Proof.
apply cat_mk with (Obj := Obj_Mon) (Hom := Hom_Mon) (Id := Id_Mon) (Compose := @Compose_Mon).
apply assoc_Mon.
apply id_1_Mon.
apply id_2_Mon.
Defined.
