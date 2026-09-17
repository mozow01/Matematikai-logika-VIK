(* Ellentmondás: A és Neg A együtt Fal tanúsítványát adják. *)

Require Import Coq.Lists.List.
Import ListNotations.

Inductive Boole : Type :=
| Tru : Boole
| Fal : Boole
| Ite : Boole -> Boole -> Boole -> Boole.

Definition Neg (A : Boole) : Boole := Ite A Fal Tru.

Inductive prg : list Boole -> Boole -> Type :=
| vz : forall (G : list Boole) (A : Boole), prg (A :: G) A
| vs : forall (G : list Boole) (A B : Boole), prg G A -> prg (B :: G) A
| tt : forall (G : list Boole), prg G Tru
| abs : forall (G : list Boole) (A : Boole), prg G Fal -> prg G A
| iteI : forall (G : list Boole) (A B C : Boole),
    prg (A :: G) B -> prg (Neg A :: G) C -> prg G (Ite A B C)
| iteTru : forall (G : list Boole) (A B C : Boole),
    prg G (Ite A B C) -> prg G A -> prg G B
| iteFal : forall (G : list Boole) (A B C : Boole),
    prg G (Ite A B C) -> prg G (Neg A) -> prg G C
| iteSame : forall (G : list Boole) (A D : Boole),
    prg G (Ite A D D) -> prg G D.

(* Miért írjuk meg? Az abs-hoz Fal kell, miközben gyakran külön A és Neg A
   útlevelünk van. A contradictionI ezekből készíti el az újrahasználható
   Fal-útlevelet, amely később bármely cél felé továbbvezethet. *)
Definition contradictionI
  {G : list Boole} {A : Boole}
  (a : prg G A) (na : prg G (Neg A)) : prg G Fal :=
  iteTru G A Fal Tru na a.

(* Ez a példa megmutatja, hogyan olvassuk ki a két szükséges tanúsítványt a
   kontextus két különböző helyéről. *)
Definition contradiction_pelda (A : Boole) : prg [Neg A; A] Fal :=
  contradictionI
    (A := A)
    (vs [A] A (Neg A) (vz [] A))
    (vz [A] (Neg A)).
