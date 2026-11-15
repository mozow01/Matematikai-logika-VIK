Definition SetU (U : Type) := U -> Prop.


Definition isin {U : Type} (x : U) (A : SetU U) := A x.

Notation "x ∈ A" := (isin x A) (at level 70, no associativity) : type_scope.


Definition union {U : Type} (A B : SetU U) := fun x => A x \/ B x.

Notation "A ∪ B" := (union A B) (at level 70, no associativity) : type_scope.


Definition intersection {U : Type} (A B : SetU U) := fun x => A x /\ B x.

Notation "A ∩ B" := (intersection A B) (at level 70, no associativity) : type_scope.


Definition complementer {U : Type} (A : SetU U) := fun x => ~ A x.

Notation "∁ A" := (complementer A) (at level 70, no associativity) : type_scope.


Definition empty {U : Type} := fun (x : U) => False.

Notation "∅" := empty (at level 70, no associativity) : type_scope.


Definition full {U : Type} := fun (x : U) => True.

Notation "⊤" := empty (at level 70, no associativity) : type_scope.


Definition subset {U : Type} (A B : SetU U) := forall x : U, (x ∈ A) -> (x ∈ B).

Notation "A ⊆ B" := (subset A B) (at level 70, no associativity) : type_scope.


Definition seteq {U : Type} (A B : SetU U) := (forall x : U, ((x ∈ A) -> (x ∈ B))) /\ (forall x : U, (x ∈ B) -> (x ∈ A)).

Notation "A ≡ B" := (seteq A B) (at level 70, no associativity) : type_scope.


Lemma seteq_refl : forall {U : Type} (A : SetU U), A ≡ A.
Proof.
  intros U A.
  unfold seteq.
  split. all: intros x H; assumption.
Qed.


Lemma seteq_sym : forall {U : Type} (A B : SetU U), A ≡ B -> B ≡ A.
Proof.
  intros U A B H.
  unfold seteq in *.
  split.
  destruct H as [HAB HBA].
  all: auto.
  all: firstorder.
Qed.


Lemma seteq_trans : forall {U : Type} (A B C : SetU U), A ≡ B -> B ≡ C -> A ≡ C.
Proof.
  intros U A B C HAB HBC.
  unfold seteq in *.
  destruct HAB as [HAB HBA].
  destruct HBC as [HBC HCB].
  split.
  - intros x H. apply HBC. apply HAB. assumption.
  - intros x H. apply HBA. apply HCB. assumption.
Qed.


Require Import Coq.Setoids.Setoid.
(*Require Import Coq.Classes.RelationClasses.*)

Add Parametric Relation {U : Type} : (SetU U) (@seteq U)
  reflexivity proved by (@seteq_refl U)
  symmetry proved by (@seteq_sym U)
  transitivity proved by (@seteq_trans U)
  as seteq_rel.

(* Pre-Boole-algebra struktúra *)
Structure BooleanAlgebra := mk_b {
  B : Type;
  Tru : B; (* true *)
  Fal : B; (* false *)
  And : B -> B -> B; (* conjunction *)
  Or : B -> B -> B; (* disjunction *)
  Neg : B -> B; (* negation *)

(* Boole-algebra axiómák *)

(* Commutativity *)
  And_comm : forall x y : B, And x y = And y x;
  Or_comm : forall x y : B, Or x y = Or y x;

(*
 Associativity 
  And_assoc : forall x y z : B, And x (And y z) = And (And x y) z;
  Or_assoc : forall x y z : B, Or x (Or y z) = Or (Or x y) z;

  

  (* Distributivity *)
  And_Or_distr : forall x y z : B, And x (Or y z) = Or (And x y) (And x z);
  Or_And_distr : forall x y z : B, Or x (And y z) = And (Or x y) (Or x z);

  (* Identity *)
  And_Tru : forall x : B, And x Tru = x;
  Or_Fal : forall x : B, Or x Fal = x;

  (* Complement *)
  And_Neg: forall x : B, And x (Neg x) = Fal;
  Or_Neg: forall x : B, Or x (Neg x) = Tru; *)
}.

Lemma set_int_comm : forall {U : Type} (A B : SetU U), (A ∩ B) ≡ (B ∩ A).
Proof.
intros U A B.
unfold seteq.
split.
intros.
unfold isin in *.
unfold intersection in *.
split.
destruct H as [H1 H2].
all: auto.
destruct H as [H1 H2].
all: auto.
intros.
unfold isin in *.
unfold intersection in *.
split.
destruct H as [H1 H2].
all: auto.
destruct H as [H1 H2].
all: auto.
Defined.

Lemma set_uni_comm : forall {U : Type} (A B : SetU U), (A ∪ B) ≡ (B ∪ A).
Proof.
intros U A B.
unfold seteq.
split.
intros.
unfold isin in *.
unfold union in *.
destruct H as [H1|H2].
right.
all: auto.
intros.
unfold isin in *.
unfold union in *.
destruct H as [H1|H2].
right.
all: auto.
Defined.


Definition setU_BooleanAlgebra {U : Type} : BooleanAlgebra := 
{|
    B := (SetU U);
    Tru := full;
    Fal := empty;
    And := intersection;
    Or := union;
    Neg := complementer;

    And_comm := @set_int_comm_eq U;
    Or_comm := @set_uni_comm_eq U;
|}.

Axiom setequality_eq : forall {U : Type} (A B : SetU U),  (A ≡ B) -> A = B. 

Lemma set_int_comm_eq : forall {U : Type} (A B : SetU U), (A ∩ B) = (B ∩ A).
Proof.
intros.
apply (@setequality_eq U).
apply (@set_int_comm U).
Qed.

Lemma set_uni_comm_eq : forall {U : Type} (A B : SetU U), (A ∪ B) = (B ∪ A).
Proof.
intros.
apply (@setequality_eq U).
apply (@set_uni_comm U).
Qed.








