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
Admitted.

Theorem And_denote_2 :
  forall A B,
    denote (And2 A B) = denote (And A B).
Proof.
Admitted.

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


(* ====================================================== *)
(*                       Programok                        *)
(* ====================================================== *)
  

Inductive Prg : list Boole -> Boole -> Type :=
| vz : forall (G : list Boole) (A : Boole),
      Prg (A :: G) A
| vs : forall (G : list Boole) (A B : Boole),
      Prg G A -> Prg (B :: G) A
| tt : forall (G : list Boole),
      Prg G Tru
| abs : forall (G : list Boole) (A : Boole),
      Prg G Fal -> Prg G A
| iteI : forall (G : list Boole) (A B C : Boole),
      Prg (A :: G) B -> Prg (Neg A :: G) C -> Prg G (Ite A B C)
| iteTru : forall (G : list Boole) (A B C : Boole),
      Prg G (Ite A B C) -> Prg G A -> Prg G B
| iteFal : forall (G : list Boole) (A B C : Boole),
      Prg G (Ite A B C) -> Prg G (Neg A) -> Prg G C
| iteSame : forall (G : list Boole) (A D : Boole),
      Prg G (Ite A D D) -> Prg G D.
     
Definition weakening
  {G : list Boole} {A B : Boole}
  (I : Prg G A) : Prg (B :: G) A :=
  vs G A B I.

Definition contradictionI
  {G : list Boole} {A : Boole}
  (a : Prg G A) (na : Prg G (Neg A)) : Prg G Fal :=
  iteTru G A Fal Tru na a.
  
Definition andI
  {G : list Boole} {A B : Boole}
  (a : Prg G A) (b : Prg G B) : Prg G (And2 A B).
Proof.
  unfold And2.
  apply iteI.
  - exact (weakening (B := A) b).
  - exact (contradictionI
             (G := Neg A :: G)
             (A := A)
             (weakening (B := Neg A) a)
             (vz G (Neg A))).
Defined.


