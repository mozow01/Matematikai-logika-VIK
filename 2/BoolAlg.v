Inductive Boole : Set :=
  | igaz : Boole
  | hamis : Boole.

Definition és (b1 b2 : Boole) := 
    match b1 with 
      | igaz => match b2 with 
                  | igaz => igaz
                  | hamis => hamis
                end
      | hamis => hamis
    end.

Definition vagy b1 b2 :=
    match b1 with 
      | igaz => igaz
      | hamis => match b2 with 
                  | igaz => igaz
                  | hamis => hamis
                 end
    end.

Theorem dist_1 : forall b1 b2 b3 : Boole, és b1 (vagy b2 b3) = vagy (és b1 b2) (és b1 b3).
Proof.
induction b1, b2, b3.
all: compute; reflexivity.
Qed.

Require Import Coq.Bool.Bool.

(* Boole-algebra struktúra *)
Structure BooleanAlgebra := {
  B : Type;
  Tru : B; (* true *)
  Fal : B; (* false *)
  And : B -> B -> B; (* conjunction *)
  Or : B -> B -> B; (* disjunction *)
  Neg : B -> B; (* negation *)

  (* Boole-algebra axiómák *)
  (* Associativity *)
  And_assoc : forall x y z : B, And x (And y z) = And (And x y) z;
  Or_assoc : forall x y z : B, Or x (Or y z) = Or (Or x y) z;

  (* Commutativity *)
  And_comm : forall x y : B, And x y = And y x;
  Or_comm : forall x y : B, Or x y = Or y x;

  (* Distributivity *)
  And_Or_distr : forall x y z : B, And x (Or y z) = Or (And x y) (And x z);
  Or_And_distr : forall x y z : B, Or x (And y z) = And (Or x y) (Or x z);

  (* Identity *)
  And_Tru : forall x : B, And x Tru = x;
  Or_Fal : forall x : B, Or x Fal = x;

  (* Complement *)
  And_Neg: forall x : B, And x (Neg x) = Fal;
  Or_Neg: forall x : B, Or x (Neg x) = Tru;
}.

Print bool.

Definition bool_BooleanAlgebra : BooleanAlgebra := {|
    B := bool;
    Tru := true;
    Fal := false;
    And := andb;
    Or := orb;
    Neg := negb;
    And_assoc := andb_assoc;
    Or_assoc := orb_assoc;
    And_comm := andb_comm;
    Or_comm := orb_comm;
    And_Or_distr := andb_orb_distrib_r;
    Or_And_distr := orb_andb_distrib_r;
    And_Tru := andb_true_r;
    Or_Fal := orb_false_r;
    And_Neg := andb_negb_r;
    Or_Neg := orb_negb_r;
  |}.
