Require Import Coq.Lists.List Arith Lia.
Import ListNotations.


(* ## A nyelv rekurzív definíciója Backus–Naur-formában ## *)

(* Egy egyszerű nyelv induktív definíciója, amely csak a 'tt' (igaz), 'ff' (hamis) és a ternáris 'if p then q else r' kondicionális kifejezéseket ismeri. *)
Inductive Term : Set :=
  | tt : Term
  | ff : Term
  | if_then_else : Term -> Term -> Term -> Term.

(* Típusolási szabályok. Ebben a nagyon egyszerű nyelvben minden kifejezés jól típusozott, mondjuk: 'bool' (ez nem a beépítet bool hanem a mi saját bool-unk ). *)
Inductive has_type : Term -> Prop :=
  | T_True : has_type tt
  | T_False : has_type ff
  | T_If : forall p q r,
      has_type p ->
      has_type q ->
      has_type r ->
      has_type (if_then_else p q r).

(* Egy kényelmi jelölés a 'has_type t' kifejezésre. *)
Notation "⊢ t [:] bool" := (has_type t) (at level 40, no associativity).

(* ## Taktikák bemutatása egyszerű példákon ## *)
(* Ebben a szakaszban minden olyan Coq taktikát bemutatunk, amelyet a későbbi, bonyolultabb bizonyításokban használni fogunk. *)

(* == Taktika: apply == *)
(* Az 'apply' megpróbálja a jelenlegi bizonyítandó célt (goal) illeszteni egy hipotézis konklúziójára. Ha sikerül, a cél helyébe a hipotézis premisszái (feltételei) kerülnek. *)

Example apply_pelda_1 : ⊢ tt [:] bool.
Proof.
  (* Cél: has_type tt. T_True pontosan ezt adja vissza. Az 'apply T_True' illeszti a definíciót a célra, és mivel a T_True-nak nincsenek további feltételei, a bizonyítás kész. *)
  apply T_True.
Qed.

Example apply_pelda_2 : ⊢ (if_then_else tt ff (if_then_else ff tt ff)) [:] bool.
Proof.
Abort.

(* == Taktika: intros, refexivity == *)

(* Az 'intros' taktikát arra használjuk, hogy a cél elején lévő univerzális kvantorral (forall) vagy inplikációval (ha..., akkorral...) lekötzött változókat a feltételek közé helyezzük. 'Ha A, akkor B'-t bizonítani nem más, mint feltenni A-t és ennek esetleges felhasználásával igazolni B-t. *)

Example intros_pelda : forall (t : Term), t = t.
Proof.
  intros t.
  (*az azonosság reflexív tulajdonsága*)
  reflexivity.
Qed.

(* == Taktikák: simpl és reflexivity == *)

(* A 'simpl' taktika kiértékeli a kifejezéseket a célban,
   például végrehajtja a függvényhívásokat és a legközelebbi elérhető olyan alakban hagyja, ami még ember számára olvasható. A 'compute' mindent elvégez.*)

(* Definiáljunk egy egyszerű rekurzív függvényt a példához. A 'bonyolító függvényt' *)
Fixpoint double_if (t: Term) : Term :=
  match t with
  | tt => if_then_else tt tt tt
  | ff => if_then_else ff ff ff
  | if_then_else p q r => if_then_else (double_if p) (double_if q) (double_if r)
  end.

Example simpl_pelda : double_if tt = if_then_else tt tt tt.
Proof.
  simpl.
  reflexivity.
Qed.

(* == Taktika: unfold == *)
(* Az 'unfold' kibont egy definíciót, ha a 'simpl' nem megy, akkor előtte unfoldolni kell az elnevezést. *)

Definition TRUE_TERM := tt.

Example unfold_pelda : TRUE_TERM = tt.
Proof.
  simpl.
  unfold TRUE_TERM.
  reflexivity.
Qed.

(* == Taktika: induction == *)
(* Az 'induction' a legfontosabb taktikák egyike. Induktív adattípusokon (mint a Term) végzett bizonyításokhoz használjuk. A rekurzív eseteknél indukciós hipotézist (IH) is kapunk a rész-kifejezésekre. *)

Example induction_pelda : forall t, has_type t.
Proof.
  induction t.
  - apply T_True.
  - apply T_False.
  - apply T_If.
    + apply IHt1.
    + apply IHt2. 
    + apply IHt3. 
Qed.

(* ## Operacionális szemantika: 
      Hogyan futnak a programk és mibe érkeznek? ## *)

(* == Egy program, az OR == *) 

Definition OR (x y : Term) := if_then_else x tt y.

(*
Definition OR_2 (x y : Term) := if_then_else x (if_then_else y tt tt) (if_then_else y tt ff).
*)

(* == A programfutás modellje: beta-redukció*)

Fixpoint beta_reduce (t : Term) : Term :=
  match t with
  | tt => tt
  | ff => ff
  | if_then_else p q r =>
      match beta_reduce p with
      | tt => beta_reduce q
      | ff => beta_reduce r
      | p' => if_then_else p' q r (* Ez az ág sosem érhető el, ha p jól tipizált *)
      end
  end.

(* A 'Compute' egy parancs, kiszámolja és kiírja egy kifejezés értékét. *)
Compute beta_reduce (if_then_else ff (if_then_else ff ff tt) tt).

(* Az 'Eval simpl in ...' szintén egy parancs, ami a 'simpl' stratégiát alkalmazva értékel ki egy kifejezést. *)
Eval simpl in beta_reduce (if_then_else ff (if_then_else ff ff tt) tt).

Example example3 : beta_reduce (if_then_else ff (if_then_else ff ff tt) tt) = tt.
Proof.
  simpl.
  reflexivity.
Qed.

Parameter y : Term.

Compute beta_reduce (OR ff y).

Lemma Or_first_true : beta_reduce (OR tt y) = tt.
Proof.
  reflexivity.
Qed.

Lemma Or_first_false : forall y, beta_reduce (OR ff y) = beta_reduce y.
Proof.
  induction y.
  all: simpl.
  all: reflexivity.
Qed.

(* == Az operacionális szemantika definíciója == *)

Definition op_val (t : Term) := beta_reduce t.

Definition is_normal (t : Term) : Prop := t = tt \/ t = ff.

(* == Taktikák: left / right  == *)
(* Ha a cél egy diszjunkció (vagy, \/), akkor a 'left' taktikával kiválaszthatjuk a bal oldali, a 'right' taktikával pedig a jobb oldali állítás bizonyítását. *)

Example left_pelda_1 : is_normal tt.
Proof.
  unfold is_normal.
  left.
  reflexivity.
Qed.

Example right_pelda_2 : is_normal ff.
Proof.
  unfold is_normal. 
  right.
  reflexivity.
Qed.

Theorem weak_normalization : forall t : Term, is_normal (beta_reduce t).
Proof.
  induction t.
  - compute.
    unfold is_normal; left; reflexivity.
  - compute.
    unfold is_normal; right; reflexivity.
  - elim IHt1.
    + intros H. 
      simpl.
      rewrite H.
      exact IHt2.
    + intros H.
      simpl.
      rewrite H.
      exact IHt3.
Defined.


(* Kis lépéses (small-step) kiértékelés: egyszerre csak egyetlen
   redukciós lépést hajt végre. *)
Fixpoint beta_reduce_small_step (t: Term) : Term :=
  match t with
  | tt => tt
  | ff => ff
  | if_then_else p q r =>
      match p with
      | tt => q
      | ff => r
      | _ => if_then_else (beta_reduce_small_step p) q r
      end
  end.

Compute beta_reduce_small_step (if_then_else (if_then_else ff ff tt) ff tt).
Compute beta_reduce_small_step (beta_reduce_small_step (if_then_else (if_then_else ff ff tt) ff tt)).

(* Kiszámolja egy kifejezés maximális beágyazási mélységét. *)
Fixpoint depth (t: Term) : nat :=
  match t with
  | tt => 0
  | ff => 0
  | if_then_else p q r => S (max (depth p) (max (depth q) (depth r)))
  end.

Compute depth (if_then_else (if_then_else ff ff tt) ff tt).

(* Egy "motor", ami n-szer alkalmazza a kis lépéses kiértékelést. *)
Fixpoint engine (n : nat) (t : Term) : Term :=
  match n with
  | 0 => t
  | S n => engine n (beta_reduce_small_step t)
  end.

(* A teljes kiértékelés a mélységgel korlátozott számú kis lépéssel. *)
Definition full_reduce t := engine (depth t) t.

Compute full_reduce (beta_reduce_small_step (if_then_else (if_then_else ff ff tt) ff tt)).

(* Erős normalizációs tétel: bárhogy beta-redukálunk, normálformához jutunk féves lépésben.*)
