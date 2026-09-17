(* 1. példa: a Boole-kifejezések absztrakt szintaxisa. *)

Inductive Boole : Type :=
| Tru : Boole
| Fal : Boole
| Ite : Boole -> Boole -> Boole -> Boole.

Check Boole.
Check Tru.
Check Fal.
Check Ite.

Definition syntax_pelda : Boole :=
  Ite (Ite Fal Tru Fal) Tru Fal.

Check syntax_pelda.
Print syntax_pelda.

(* Az összetett fa nem azonos a Fal levéllel. *)
Example syntax_pelda_nem_Fal :
  syntax_pelda <> Fal.
Proof.
  unfold syntax_pelda.
  discriminate.
Qed.
