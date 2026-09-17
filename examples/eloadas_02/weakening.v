(* Weakening: az útlevél egy bővebb környezetben is érvényes. *)

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

(* Miért írjuk meg? Az iteI ágai új feltevést tesznek a kontextus elé, ezért
   a korábban megszerzett útlevelet rendszeresen vastagabb iratmappába kell
   átvinnünk. Ezt az adminisztrációt csomagolja el a weakening. *)
Definition weakening
  {G : list Boole} {A B : Boole}
  (I : prg G A) : prg (B :: G) A :=
  vs G A B I.

(* Ez a példa megmutatja, hogy az új A iratot nem kötelező felhasználni. *)
Definition weakening_pelda (A : Boole) : prg [A] Tru :=
  weakening (B := A) (tt []).

(* Miért mutatjuk meg újra? A taktikás alak láthatóvá teszi, hogy a Proof
   mód ugyanazt a programot építi fel, mint a közvetlen vs-kifejezés. *)
Definition weakening_taktikaval
  {G : list Boole} {A B : Boole}
  (I : prg G A) : prg (B :: G) A.
Proof.
  apply vs.
  exact I.
Defined.
