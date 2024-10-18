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
  split; intros x H; assumption.
Qed.


Lemma seteq_sym : forall {U : Type} (A B : SetU U), A ≡ B -> B ≡ A.
Proof.
  intros U A B H.
  unfold seteq in *.
  destruct H as [HAB HBA].
  split; assumption.
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

Lemma problem_1 : forall U (A B C : @SetU U), (A ∪ (B ∩ C)) ≡ ((A ∪ B) ∩ C) <-> A ⊆ C.
Proof.
unfold subset; unfold seteq; unfold intersection; unfold union; unfold isin.
firstorder. 
Qed.

Lemma problem_2 : forall U (A B C : @SetU U), (A ∪ (B ∩ C)) ≡ ((A ∪ B) ∩ C) <-> A ⊆ C.
Proof.
unfold subset; unfold seteq; unfold intersection; unfold union; unfold isin.
firstorder. 
Qed.






