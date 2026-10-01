Require Import Coq.Arith.Arith.
Require Import Lia.

Inductive bintree :=
    | leaf : bintree
    | node : bintree -> bintree -> bintree.

    (*
                \/   
    \/         \/
    
    *)

Definition Tree1 :=  node leaf leaf.

Check Tree1.

Definition Tree2 :=  node leaf (node leaf leaf).

Fixpoint oplus t1 t2 : bintree :=
   match t1 with 
     | leaf => t2
     | node t' t'' => node t' (oplus t'' t2)
   end.

Notation "t1 ⊕ t2" :=
  (oplus t1 t2)
  (left associativity, at level 50).

Theorem neutral1 : forall (t : bintree), (leaf ⊕ t) = t.
Proof.
intros.
compute.
reflexivity.
Qed.

Theorem neutral2 : forall (t : bintree), (t ⊕ leaf) = t.
Proof.
intros. 
induction t.
  * compute. auto.
  * simpl. 
    rewrite IHt2.
    auto.
Qed.

Theorem oplus_assoc : forall (t1 t2 t3 : bintree), 
    ((t1 ⊕ t2) ⊕ t3) = (t1 ⊕ (t2 ⊕ t3)).
Proof.
intros.
induction t1.
 * simpl. auto.
 * simpl.
   rewrite IHt1_2.
   auto.
Qed.

Fixpoint leaflength t : nat :=
   match t with 
     | leaf => 1
     | node t1 t2 => (leaflength t1) + (leaflength t2)
   end.

Compute leaflength Tree2.

Theorem ll_1 : leaflength leaf = 1.
Proof.
compute. auto.  

(*
HF
Theorem ll_2 : ?? 

HF oplus és a ll kapcsolata.
*)

