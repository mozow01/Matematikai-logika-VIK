Require Import List Arith Peano Lia.
Import ListNotations.

Inductive Fm : Set :=
  | Ato : nat -> Fm
  | Fal : Fm
  | Imp : Fm -> Fm -> Fm.

Notation "x ⇒ y" := (Imp x y) (at level 90, right associativity) :
type_scope.

Inductive Pf : Set :=
  | hyp : nat -> Pf
  | impi : Fm -> Pf -> Pf
  | impe : Pf -> Pf -> Pf
  | negi : Fm -> Pf -> Pf
  | negc : Pf -> Pf.

Definition Cntxt := list Fm.

Inductive Prov : Cntxt -> Pf -> Fm -> Prop :=
  | ND_hypO : forall Γ A, Prov (A :: Γ) (hyp 0) A
  | ND_hypS :
      forall Γ A B i,
      Prov Γ (hyp i) A -> Prov (B :: Γ) (hyp (S i)) A
  | ND_impi :
      forall Γ t A B,
      Prov (A :: Γ) t B -> Prov Γ (impi A t) (Imp A B)
  | ND_impe :
      forall Γ t s A B,
      Prov Γ t (Imp A B) -> Prov Γ s A -> Prov Γ (impe t s) B
  | ND_negi :
      forall Γ t A,
      Prov Γ t Fal -> Prov Γ (negi A t) A
  | ND_negc :
      forall Γ t A,
      Prov Γ t (Imp (Imp A Fal) Fal) -> Prov Γ (negc t) A.

Notation "G ⊢ t [:] A" := (Prov G t A) (at level 70, no associativity) : type_scope.

(* Értékelés definíciója *)
Fixpoint eval (v : nat -> bool) (A : Fm) : bool :=
  match A with
  | Ato n => v n
  | Fal => false
  | Imp A B => (negb (eval v A)) || (eval v B)
  end.

Lemma id_bool : forall (x : bool), ((negb x) || x)%bool = true.
Proof. 
induction x.
all: simpl; auto.
Qed.

Lemma id_eval : forall (v : nat -> bool) A, eval v (A ⇒ A) = true.
Proof. 
intros.
simpl.
rewrite id_bool.
auto.
Qed.

(* Modellezi reláció definíciója *)
Definition models (v : nat -> bool) (G : Cntxt) (A : Fm) : Prop :=
  (forall B, In B G -> eval v B = true) -> eval v A = true.

Notation "G ⊨ A ← v" := (models v G A) (at level 70, no associativity) : type_scope.

Lemma id_models : forall (v : nat -> bool) A, nil ⊨ (A ⇒ A) ← v.
Proof. 
intros.
unfold models.
intros.
rewrite id_eval.
auto.
Qed.

Lemma id_Coq : forall (A : Prop), A -> A.
Proof.
intros.
exact H. 
Show Proof.
(*(fun (A : Prop) (H : A) => H)*)
Qed.

Lemma id_ND : forall A, exists t, nil ⊢ t [:] (A ⇒ A).
Proof.
intros.
exists (impi A (hyp 0)).
apply ND_impi.
apply ND_hypO.
Qed.

(* Helyességi tétel *)
Theorem soundness : forall G A, (exists t, G ⊢ t [:] A) -> forall v, G ⊨ A ← v.
Proof.
Admitted.

(* Teljességi tétel *)
Theorem completeness : forall G A, (forall v, G ⊨ A ← v) -> (exists t, G ⊢ t [:] A).
Proof.
Admitted.

