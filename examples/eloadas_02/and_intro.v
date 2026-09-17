(* Konjunkció bevezetése: két útlevélből egy közös útlevél. *)

Require Import Coq.Lists.List.
Import ListNotations.

Inductive Boole : Type :=
| Tru : Boole
| Fal : Boole
| Ite : Boole -> Boole -> Boole -> Boole.

Definition Neg (A : Boole) : Boole := Ite A Fal Tru.
Definition And2 (A B : Boole) : Boole := Ite A B Fal.

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

(* Az andI igaz ágában egy régi B-útlevelet kell az új A feltevés mellett
   használnunk; ezt az ismétlődő kontextusbővítést csomagolja el a weakening. *)
Definition weakening
  {G : list Boole} {A B : Boole}
  (I : prg G A) : prg (B :: G) A :=
  vs G A B I.

(* Az andI hamis ágában A és Neg A egyszerre áll rendelkezésre. Ebből a
   segédprogram készít Fal-útlevelet, pontosan az ág kívánt célját. *)
Definition contradictionI
  {G : list Boole} {A : Boole}
  (a : prg G A) (na : prg G (Neg A)) : prg G Fal :=
  iteTru G A Fal Tru na a.

(* Miért írjuk meg? A kliens egy A- és egy B-útlevelet szeretne egyetlen
   And2 A B útlevélbe csomagolni anélkül, hogy ismerné az And2 belső
   Ite-kódolását. Az andI elrejti a szükséges adminisztrációt. *)
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

(* Ez a példa mutatja az andI nyereségét: a használónak már nem kell
   kibontania az And2 Ite-kódolását. Csak átadja a két útlevelet. *)
Definition andI_pelda (A B : Boole) : prg [B; A] (And2 A B) :=
  andI
    (vs [A] A B (vz [] A))
    (vz [A] B).
