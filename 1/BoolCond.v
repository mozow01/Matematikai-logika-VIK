Require Import Coq.Lists.List Arith.
Import ListNotations.

(* Ternáris kondicionális nyelvének induktív definíciója *)

(*
Inductive Term : Set := tt | ff | if_then_else : Term -> Term -> Term -> Term.
 *)

Inductive Term : Set :=
  | tt : Term
  | ff : Term
  | if_then_else : Term -> Term -> Term -> Term.

(* Típusolási szabályok *)

Inductive has_type : Term -> Prop :=
  | T_True : has_type tt
  | T_False : has_type ff
  | T_If : forall p q r,
      has_type p ->
      has_type q ->
      has_type r ->
      has_type (if_then_else p q r).

Notation "⊢ t [:] bool" := (has_type t) (at level 40, no associativity).

(*

-------------         --------------
  ⊢ tt : bool          ⊢ ff : bool

  ⊢ x : bool   ⊢ q : bool   ⊢ r: bool
------------------------------------
     ⊢ if_then_else x q r : bool

*)


(* Példák a típusolás használatára *)
Example example1 : ⊢ tt [:] bool.
Proof.
  apply T_True.
Qed.

Example example2 : ⊢ (if_then_else ff tt ff) [:] bool.
Proof.
  apply T_If.
  apply T_False.
  apply T_True.
  apply T_False.
Qed.

Example term : ⊢ (if_then_else tt (if_then_else tt ff tt) ff) [:] bool.
Proof.
  apply T_If.
  apply T_True.
  apply T_If.
  apply T_True.
  apply T_False.
  apply T_True.
  apply T_False.
Qed.

Definition OR_1 (x y : Term) := if_then_else x tt y. 

(*
Example ex_1 : forall (y : Term), (if_then_else tt tt y) = tt.
Proof.
intros.
induction y.
Abort.
*)

Reserved Notation "⊢ t ≡ s" (at level 70, no associativity).

Inductive D_equiv : Term -> Term -> Prop :=
  | E_Refl : forall t,
      ⊢ t ≡ t 
  | E_Symm : forall t s,
      ⊢ t ≡ s ->
      ⊢ s ≡ t
  | E_Trans : forall t s u,
      ⊢ t ≡ s  ->
      ⊢ s ≡ u  ->
      ⊢ t ≡ u 
  | E_If : forall p1 p2 q1 q2 r1 r2,
      ⊢ p1 ≡ p2  ->
      ⊢ q1 ≡ q2  ->
      ⊢ r1 ≡ r2  ->
      ⊢ (if_then_else p1 q1 r1) ≡ (if_then_else p2 q2 r2)
  | E_beta_True : forall p q,
      ⊢ (if_then_else tt p q) ≡ p
  | E_beta_False : forall p q,
      ⊢ (if_then_else ff p q) ≡ q
where "⊢ t ≡ s" := (D_equiv t s).


Fixpoint beta_reduct (t : Term) : Term :=
 match t with 
   | if_then_else p q r => 
       match p with
         | tt => beta_reduct q
         | ff => beta_reduct r
         | _  => if_then_else (beta_reduct p) (beta_reduct q) (beta_reduct r) 
       end
   | tt => tt
   | ff => ff
 end.

Eval compute in 
beta_reduct (if_then_else tt (if_then_else ff (if_then_else ff ff tt) tt) tt ).

Lemma beta_1 : forall q r, 
⊢ beta_reduct (if_then_else tt q r) ≡ beta_reduct q.
Proof.
intros.
simpl.
apply E_Refl.
Qed.

Example ex_1 : forall (y : Term), ⊢ (if_then_else ff tt y) ≡ y.
Proof.
intros.
apply E_beta_False.
Qed.

Example ex_2 : forall (x : Term), ⊢ (if_then_else x tt ff) ≡ x.
Proof.
intros.
(*
apply E_beta_False.
*)
Abort.

Eval compute in 
beta_reduct (if_then_else (if_then_else ff (if_then_else ff ff tt) tt) ff tt ).

Eval compute in 
beta_reduct (if_then_else (if_then_else (if_then_else ff ff tt) ff tt) ff tt ).

Fixpoint depth (t : Term) : nat :=
  match t with
  | tt => 0
  | ff => 0
  | if_then_else p q r => 
      1 + max (depth p) (max (depth q) (depth r))
  end.

Fixpoint beta_reduct_aux (n : nat) (t : Term) : Term :=
  match n with 
    | 0 => beta_reduct t
    | S m => beta_reduct (beta_reduct_aux m t)
  end.

Definition beta_reduct_full (t : Term) := beta_reduct_aux (depth t) t.

Eval compute in beta_reduct_full (if_then_else (if_then_else (if_then_else ff ff tt) ff tt) ff tt ).

(*Shunting Yard is kiértékeli*)

Theorem WeakNormalization : forall t : Term, beta_reduct_full t = tt \/ beta_reduct_full t = ff.
Proof.
Admitted.


Fixpoint denote_sem (t : Term) : bool :=
 match t with 
  | if_then_else p q r => if (denote_sem p) then (denote_sem q) else (denote_sem r)
  | tt => true
  | ff => false
 end.

Definition w := (fun (n : nat) => true). 