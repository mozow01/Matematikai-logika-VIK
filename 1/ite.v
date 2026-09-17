Require Import Coq.Lists.List Arith Lia.
Import ListNotations.

Inductive Boole : Type :=
| Tru  : Boole
| Fal  : Boole
| Ite  : Boole -> Boole -> Boole -> Boole.

Definition Neg (A : Boole) : Boole :=
  Ite A Fal Tru.
  
Definition And (A B : Boole) : Boole :=
  Ite A (Ite B Tru Fal) Fal.
 
Definition And2 (A B : Boole) : Boole :=
  Ite A B Fal.
   
(* ====================================================== *)
(*               Denotációs szemantika                    *)
(* ====================================================== *)

Fixpoint denote (A : Boole) : bool :=
  match A with
  | Tru => true
  | Fal => false
  | Ite A B C =>
      if denote A then denote B else denote C
  end.
  
Compute denote (And Tru Fal).

Theorem And_denote :
  forall A B,
    denote (And2 A B) = andb (denote A) (denote B).
Proof.
  intros A B.
  unfold And2.
  simpl.
  destruct (denote A); reflexivity.
Qed.

Theorem And_denote_2 :
  forall A B,
    denote (And2 A B) = denote (And A B).
Proof.
  intros A B.
  unfold And2, And.
  simpl.
  destruct (denote A), (denote B); reflexivity.
Qed.

(* ====================================================== *)
(*               Operacionális szemantika                 *)
(* ====================================================== *)

Fixpoint beta_reduce (A : Boole) : Boole :=
  match A with
  | Tru => Tru
  | Fal => Fal
  | Ite A B C =>
      match beta_reduce A with
      | Tru => beta_reduce B
      | Fal => beta_reduce C
      | A' => Ite A' B C
      end
  end.
  
Compute beta_reduce (Ite Tru Fal Tru).

Compute beta_reduce (Ite (Ite Fal Fal Tru) Tru Fal).

Example beta_pelda : beta_reduce (Ite Fal (Ite Fal Fal Tru) Tru) = Tru.
Proof.
  simpl.
  reflexivity.
Qed.


(* ====================================================== *)
(*                    Normálformák                        *)
(* ====================================================== *)

Definition is_normal (A : Boole) : Prop :=
  A = Tru \/ A = Fal.

Example Tru_normal :
  is_normal Tru.
Proof.
  unfold is_normal.
  left.
  reflexivity.
Qed.


Example Fal_normal :
  is_normal Fal.
Proof.
  unfold is_normal.
  right.
  reflexivity.
Qed.


(* ====================================================== *)
(*                 Gyenge normalizáció                    *)
(* ====================================================== *)

(* Minden Boole kifejezés teljes beta-redukciójának
   eredménye Tru vagy Fal. *)

Theorem weak_normalization :
  forall A : Boole,
    is_normal (beta_reduce A).
Proof.
  induction A.
  - unfold is_normal.
    left.
    reflexivity.
  - unfold is_normal.
    right.
    reflexivity.
  - simpl.
    destruct IHA1.
    + rewrite H.
      exact IHA2.
    + rewrite H.
      exact IHA3.
Qed.


(* ====================================================== *)
(*     A denotáció és a beta-redukció felcserélhető       *)
(* ====================================================== *)

(*

              beta_reduce
       A --------------------> beta_reduce A
       |                              |
 denote|                              |denote
       v                              v
     bool --------------------------> bool
                  identitás

   Vagyis a beta-redukció nem változtatja meg
   a kifejezés Boole-jelentését.
*)

Theorem denote_beta :
  forall A : Boole,
    denote (beta_reduce A) = denote A.
Proof.
  induction A.
  - reflexivity.
  - reflexivity.
  - simpl.
    destruct (beta_reduce A1) eqn:H.
    + simpl in IHA1.
      rewrite <- IHA1.
      simpl.
      exact IHA2.
    + simpl in IHA1.
      rewrite <- IHA1.
      simpl.
      exact IHA3.
    + simpl in IHA1.
      simpl.
      rewrite IHA1.
      reflexivity.
Qed.
