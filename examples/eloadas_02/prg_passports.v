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

(* Egy már meglévő tanúsítvány egy új feltételezés felvétele után is érvényes. *)
Definition weakening
  {G : list Boole} {A B : Boole}
  (I : prg G A) : prg (B :: G) A :=
  vs G A B I.

(* A és Neg A együtt ellentmondást, azaz Fal tanúsítványát adják. *)
Definition contradictionI
  {G : list Boole} {A : Boole}
  (a : prg G A) (na : prg G (Neg A)) : prg G Fal :=
  iteTru G A Fal Tru na a.

(* Két tanúsítványból elkészítjük az And2 A B tanúsítványát. *)
Definition andI
  {G : list Boole} {A B : Boole}
  (a : prg G A) (b : prg G B) : prg G (And2 A B).
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

(* Két apró útlevélpélda: a típusuk mondja meg, hová engednek be. *)
Definition igaz_utlevel : prg [] Tru :=
  tt [].

Definition elso_feltetelezes
  (A B : Boole) : prg [A; B] A :=
  vz [B] A.
