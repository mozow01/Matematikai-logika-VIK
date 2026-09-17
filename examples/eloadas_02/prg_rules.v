(* A prg konstruktorai: nyolc útlevél-kiállítási szabály. *)

Require Import Coq.Lists.List.
Import ListNotations.

Inductive Boole : Type :=
| Tru : Boole
| Fal : Boole
| Ite : Boole -> Boole -> Boole -> Boole.

Definition Neg (A : Boole) : Boole := Ite A Fal Tru.

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

Check vz.
Check vs.
Check tt.
Check abs.
Check iteI.
Check iteTru.
Check iteFal.
Check iteSame.

(* Miért írjuk le ezeket a példákat? Nem új szabályokat vezetünk be, hanem
   minimális használati sablont adunk mind a nyolc konstruktorhoz. *)

(* vz: a környezet első bejegyzéséből útlevelet állítunk ki. *)
Definition vz_pelda (G : list Boole) (A : Boole) : prg (A :: G) A :=
  vz G A.

(* vs: egy régi útlevél egy elé írt, új feltételezés mellett is használható. *)
Definition vs_pelda
  (G : list Boole) (A B : Boole) (p : prg G A) : prg (B :: G) A :=
  vs G A B p.

(* tt: Tru minden környezetben beléphet. *)
Definition tt_pelda (G : list Boole) : prg G Tru :=
  tt G.

(* abs: ha Fal bejutott, bármely A-hoz készíthető tanúsítvány. *)
Definition abs_pelda
  (G : list Boole) (A : Boole) (p : prg G Fal) : prg G A :=
  abs G A p.

(* iteI: akkor készíthetünk feltételes útlevelet, ha mindkét lehetséges
   ághoz előre van ellenőrzött útvonalunk. *)
Definition iteI_pelda
  (G : list Boole) (A B C : Boole)
  (p : prg (A :: G) B) (q : prg (Neg A :: G) C) :
  prg G (Ite A B C) :=
  iteI G A B C p q.

(* iteTru: A tanúsítványa kiválasztja a feltételes igaz ágát. *)
Definition iteTru_pelda
  (G : list Boole) (A B C : Boole)
  (p : prg G (Ite A B C)) (a : prg G A) : prg G B :=
  iteTru G A B C p a.

(* iteFal: Neg A tanúsítványa a feltételes hamis ágát választja ki. *)
Definition iteFal_pelda
  (G : list Boole) (A B C : Boole)
  (p : prg G (Ite A B C)) (na : prg G (Neg A)) : prg G C :=
  iteFal G A B C p na.

(* iteSame: azonos úti céloknál a prg szabálya megengedi a feltétel
   elfelejtését; ehhez nem kell A-t kiértékelnünk. *)
Definition iteSame_pelda
  (G : list Boole) (A D : Boole)
  (p : prg G (Ite A D D)) : prg G D :=
  iteSame G A D p.
