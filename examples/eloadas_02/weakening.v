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

Definition weakening
  {G : list Boole} {A B : Boole}
  (I : prg G A) : prg (B :: G) A :=
  vs G A B I.

(* A Tru-útlevél egy tetszőleges új feltételezés után is használható. *)
Definition weakening_pelda (A : Boole) : prg [A] Tru :=
  weakening (B := A) (tt []).

(* Ugyanez taktikákkal: a cél típusa vezeti az építkezést. *)
Definition weakening_taktikaval
  {G : list Boole} {A B : Boole}
  (I : prg G A) : prg (B :: G) A.
Proof.
  apply vs.
  exact I.
Defined.
