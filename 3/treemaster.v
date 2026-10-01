Require Import Coq.Arith.Arith.


(* ====================================================== *)
(*                    Binaris fak                         *)
(* ====================================================== *)

Inductive bintree : Type :=
| leaf : bintree
| node : bintree -> bintree -> bintree.


(* A fa leveleinek szama. *)
Fixpoint leaflength (t : bintree) : nat :=
  match t with
  | leaf => 1
  | node t1 t2 => leaflength t1 + leaflength t2
  end.


(* A level magassaga 0. Egy node magassaga a ket reszfa
   magassaganak maximumanal eggyel nagyobb. *)
Fixpoint height (t : bintree) : nat :=
  match t with
  | leaf => 0
  | node t1 t2 => 1 + Nat.max (height t1) (height t2)
  end.


(* t1 \oplus t2 a t2 fat a t1 legjobboldalibb
   levelenek helyere teszi. *)
Fixpoint oplus (t1 t2 : bintree) : bintree :=
  match t1 with
  | leaf => t2
  | node t11 t12 => node t11 (oplus t12 t2)
  end.

Notation "t1 ⊕ t2" :=
  (oplus t1 t2)
  (left associativity, at level 50). 
