Require Import Coq.Arith.Arith.
Require Import Lia.
(*n magasságú fa, ami különböző magasságú ágakból áll*)
Inductive HTree : nat -> Set :=
  | Hleaf : HTree 0
  | Hnode : forall n m : nat, HTree n -> HTree m -> HTree (S (max n m)).

(* pl.: *)

Check Hnode 1 0 (Hnode 0 0 Hleaf Hleaf) Hleaf.

(*... mert ez kiszámolja*)
Compute ( HTree
(S
(Init.Nat.max 1
0))).

Fixpoint Height (n : nat) (t : HTree n) : nat :=
  match t with
    | Hleaf => 0
    | Hnode n m t1 t2 => (max (Height n t1) (Height m t2)) + 1
  end.

Lemma Height_lemma : forall (n : nat) (t : HTree n), Height n t = n.
Proof.
intros.
induction t.
- compute; auto.
- simpl.
  rewrite IHt1.
  rewrite IHt2.
  lia.
Defined.

(* A fa tükörképe: minden csomópontban felcseréljük a két ágat.
   A visszatérési típus azt is tanúsítja, hogy a magasság nem változik. *)
Fixpoint Hrevert (n : nat) (t : HTree n) {struct t} : HTree n.
Proof.
  destruct t.

  - apply Hleaf.

  - rewrite Nat.max_comm.
    apply Hnode.

    + apply Hrevert.
      exact t2.

    + apply Hrevert.
      exact t1.
Defined.


Inductive Exp : Set :=
  | AT : nat -> Exp  
  | NOT : Exp -> Exp
  | AND : Exp -> Exp -> Exp 
  | OR : Exp -> Exp -> Exp.

Inductive UnOp : Set :=
  | NOT_c : UnOp.

Inductive BinOp : Set :=
  | AND_c : BinOp
  | OR_c : BinOp.

Inductive AST : Set :=
  | leaf : nat -> AST
  | node1 : UnOp -> AST -> AST
  | node2 : BinOp -> AST -> AST -> AST.

Definition ex_1 := node2 AND_c (leaf 2) (leaf 3).

Print ex_1.

Fixpoint ExpDenote (e : Exp) (v : nat -> bool ) {struct e} :=
match e with 
  | AT n => v n 
  | NOT e1 => negb (ExpDenote e1 v)
  | AND e1 e2 => andb (ExpDenote e1 v) (ExpDenote e2 v)
  | OR e1 e2 => orb (ExpDenote e1 v) (ExpDenote e2 v)
end.

Fixpoint ASTDenote (t: AST) (v : nat -> bool ) {struct t} :=
match t with
  | leaf n => v n
  | node1 _ t1 => negb (ASTDenote t1 v)
  | node2 x t1 t2 => match x with
           | AND_c => andb (ASTDenote t1 v) (ASTDenote t2 v)
           | OR_c => orb (ASTDenote t1 v) (ASTDenote t2 v)
                     end
end.

Fixpoint Translater1 (e : Exp) : AST :=
match e with
  | AT n => leaf n 
  | NOT e1 => node1 NOT_c (Translater1 e1)
  | AND e1 e2 => node2 AND_c (Translater1 e1) (Translater1 e2)
  | OR e1 e2 => node2 OR_c (Translater1 e1) (Translater1 e2)
end.

Fixpoint Translater2 (t : AST) :=
match t with
  | leaf n => AT n
  | node1 _ t1 => NOT (Translater2 t1)
  | node2 AND_c t1 t2 => AND (Translater2 t1) (Translater2 t2)
  | node2 OR_c t1 t2 => OR (Translater2 t1) (Translater2 t2) 
end.

Theorem Soundness1 : forall t v, ASTDenote t v = ExpDenote (Translater2 t) v.
Proof.
intros.
induction t.
compute.
auto.
simpl.
rewrite IHt.
auto.
induction b.
all: simpl; rewrite IHt1; rewrite IHt2; auto.
Qed.

Theorem Soundness2 : forall e v, ExpDenote e v = ASTDenote (Translater1 e) v.
Proof.
