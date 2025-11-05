

(************************************************************)
(* 1. RÉSZ: A (Tree, $\oplus$, leaf) MONOID DEFINÍCIÓJA    *)
(************************************************************)

(* Az alap adattípus. *)
Inductive Tree : Type :=
  | leaf : Tree
  | node : Tree -> Tree -> Tree.

(* A "jobb oldali beillesztés" művelete. *)
Fixpoint t_oplus (t1 t2 : Tree) : Tree :=
  match t1 with
  | leaf => t2
  | node l r => node l (t_oplus r t2)
  end.

(* Kényelmi jelölés. *)
Infix "$\oplus$" := t_oplus (at level 50, left associativity).

(* Az (Tree, $\oplus$) monoid tulajdonságainak igazolása. *)

Theorem t_oplus_assoc : forall t1 t2 t3,
  (t1 $\oplus$ t2) $\oplus$ t3 = t1 $\oplus$ (t2 $\oplus$ t3).
Proof.
  intros t1 t2 t3.
  induction t1.
  - (* Bázis: t1 = leaf *)
    simpl. reflexivity.
  - (* Lépés: t1 = node l r *)
    simpl.
    (* A cél: node l (t_oplus (t_oplus r t2) t3) = node l (t_oplus r (t_oplus t2 t3)) *)
    (* Ez f_equal-lal és az indukciós hipotézissel (IHr) azonnal kijön. *)
    rewrite IHt1_2. reflexivity.
Qed.

Theorem t_oplus_left_identity : forall t, leaf $\oplus$ t = t.
Proof.
  intros t. simpl. reflexivity.
Qed.

Theorem t_oplus_right_identity : forall t, t $\oplus$ leaf = t.
Proof.
  intros t. induction t.
  - (* Bázis: t = leaf *)
    simpl. reflexivity.
  - (* Lépés: t = node l r *)
    simpl. rewrite IHt2. reflexivity.
Qed.


(****************************************************************)
(* 2. RÉSZ: A (S_f, $\circ$, s_leaf) FÜGGVÉNY-MONOID DEFINÍCIÓJA *)
(****************************************************************)

(* A "balról hozzáfűzés" műveletek konstruktív reprezentációja.
   Ez a típus izomorf lesz a Tree-vel. *)
Inductive S_f : Type :=
  | s_leaf : S_f   (* Az identitás-függvényt (leaf $\oplus$ s) reprezentálja *)
  | s_node : Tree -> S_f -> S_f. (* A (node t f) $\oplus$ s műveletet reprezentálja *)

(* Ezen függvény-reprezentációk kompozíciója.
   Ez felel meg a (f $\circ$ g)(s) = f(g(s)) műveletnek. *)
Fixpoint s_compose (f1 f2 : S_f) : S_f :=
  match f1 with
  | s_leaf => f2
  | s_node t sub_f => s_node t (s_compose sub_f f2)
  end.

(* Kényelmi jelölés. *)
Infix "$\circ$" := s_compose (at level 55, left associativity).

(* Az (S_f, $\circ$) monoid tulajdonságainak igazolása.
   (A struktúra annyira hasonló, hogy a bizonyítások szinte azonosak.) *)

Theorem s_compose_assoc : forall f1 f2 f3,
  (f1 $\circ$ f2) $\circ$ f3 = f1 $\circ$ (f2 $\circ$ f3).
Proof.
  intros f1 f2 f3. induction f1.
  - (* Bázis: f1 = s_leaf *)
    simpl. reflexivity.
  - (* Lépés: f1 = s_node t sub_f *)
    simpl. rewrite IHf1. reflexivity.
Qed.

Theorem s_compose_left_identity : forall f, s_leaf $\circ$ f = f.
Proof.
  intros f. simpl. reflexivity.
Qed.

Theorem s_compose_right_identity : forall f, f $\circ$ s_leaf = f.
Proof.
  intros f. induction f.
  - (* Bázis: f = s_leaf *)
    simpl. reflexivity.
  - (* Lépés: f = s_node t sub_f *)
    simpl. rewrite IHf. reflexivity.
Qed.


(****************************************************************)
(* 3. RÉSZ: AZ IZOMORFIZMUS ÉS A HOMOMORFIZMUS IGAZOLÁSA      *)
(****************************************************************)

(* A leképezés Tree-ből S_f-be. (A "H" függvényünk) *)
Fixpoint H_Tree_to_Sf (t : Tree) : S_f :=
  match t with
  | leaf => s_leaf
  | node l r => s_node l (H_Tree_to_Sf r)
  end.

(* A leképezés S_f-ből Tree-be. (A "H" inverze) *)
Fixpoint H_Sf_to_Tree (f : S_f) : Tree :=
  match f with
  | s_leaf => leaf
  | s_node t sub_f => node t (H_Sf_to_Tree sub_f)
  end.

(* Igazoljuk, hogy ez a kettő tényleg egymás inverze. *)

Theorem H_iso_1 : forall t, H_Sf_to_Tree (H_Tree_to_Sf t) = t.
Proof.
  intros t. induction t.
  - simpl. reflexivity.
  - simpl. rewrite IHt2. reflexivity.
Qed.

Theorem H_iso_2 : forall f, H_Tree_to_Sf (H_Sf_to_Tree f) = f.
Proof.
  intros f. induction f.
  - simpl. reflexivity.
  - simpl. rewrite IHf. reflexivity.
Qed.

(* -- A FŐ TÉTEL --
   Igazoljuk, hogy a H leképezés egy monoid homomorfizmus,
   vagyis "tiszteletben tartja" a műveleteket. *)

Theorem H_is_monoid_homomorphism : forall t1 t2,
  H_Tree_to_Sf (t1 $\oplus$ t2) = (H_Tree_to_Sf t1) $\circ$ (H_Tree_to_Sf t2).
Proof.
  intros t1 t2.
  induction t1.
  - (* Bázis: t1 = leaf *)
    (* Cél: H(leaf $\oplus$ t2) = H(leaf) $\circ$ H(t2) *)
    simpl.
    (* Cél: H(t2) = s_leaf $\circ$ H(t2) *)
    (* Ez az s_compose definíciója (bal oldali egységelem) *)
    reflexivity.
  - (* Lépés: t1 = node l r *)
    (* Cél: H((node l r) $\oplus$ t2) = H(node l r) $\circ$ H(t2) *)
    simpl.
    (* LHS: H(node l (r $\oplus$ t2))
          = s_node l (H (r $\oplus$ t2)) *)
    (* RHS: (s_node l (H r)) $\circ$ H(t2)
          = s_node l ((H r) $\circ$ (H t2)) *)
    
    (* A célunk tehát:
       s_node l (H (r $\oplus$ t2)) = s_node l ((H r) $\circ$ (H t2))
       
       Ez leegyszerűsödik (f_equal) erre:
       H (r $\oplus$ t2) = (H r) $\circ$ (H t2)
       
       Ami PONTOSAN az indukciós hipotézis (IHr). *)
    rewrite IHt1_2.
    reflexivity.
Qed.

(* És bónuszként (bár a fenti tétel bázisesete már megmutatta):
   a leképezés az egységelemet egységelemre képezi. *)

Theorem H_preserves_identity : H_Tree_to_Sf leaf = s_leaf.
Proof.
  reflexivity.
Qed.