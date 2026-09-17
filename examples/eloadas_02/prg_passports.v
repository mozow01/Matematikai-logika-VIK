(* 2. előadás: adott típusú programok mint tanúsítványok. *)

Require Import Coq.Lists.List.
Import ListNotations.

(* A Boole nyelv, amelyből az első órán indultunk. *)
Inductive Boole : Type :=
| Tru : Boole
| Fal : Boole
| Ite : Boole -> Boole -> Boole -> Boole.

Definition Neg (A : Boole) : Boole :=
  Ite A Fal Tru.

Definition And2 (A B : Boole) : Boole :=
  Ite A B Fal.

(* A prg G A típus lakói olyan programok, amelyek tanúsítják, hogy
   az A Boole-kifejezés levezethető a G környezet feltételezéseiből. *)
Inductive prg : list Boole -> Boole -> Type :=
| vz : forall (G : list Boole) (A : Boole),
    prg (A :: G) A

| vs : forall (G : list Boole) (A B : Boole),
    prg G A -> prg (B :: G) A

| tt : forall (G : list Boole),
    prg G Tru

| abs : forall (G : list Boole) (A : Boole),
    prg G Fal -> prg G A

| iteI : forall (G : list Boole) (A B C : Boole),
    prg (A :: G) B -> prg (Neg A :: G) C -> prg G (Ite A B C)

| iteTru : forall (G : list Boole) (A B C : Boole),
    prg G (Ite A B C) -> prg G A -> prg G B

| iteFal : forall (G : list Boole) (A B C : Boole),
    prg G (Ite A B C) -> prg G (Neg A) -> prg G C

| iteSame : forall (G : list Boole) (A D : Boole),
    prg G (Ite A D D) -> prg G D.

(* Miért ezzel a két példával kezdünk? Az első megmutatja, hogy Tru falujába
   iratok nélkül is beléphetünk. A második megmutatja, hogyan lesz a mappa
   legfelső A iratából A célú útlevél. A típust mindig úticélként olvassuk. *)
Definition igaz_utlevel : prg [] Tru :=
  tt [].

Definition elso_feltetelezes
  (A B : Boole) : prg [A; B] A :=
  vz [B] A.
