Lemma problem_1 : forall (U : Type) (P : U -> U -> Prop), (exists x, forall y, P x y) -> forall y, exists x, P x y.
Proof.
intros U P H.
intros.
destruct H.
exists x.
apply H.
Show Proof.
Eval simpl in ((fun (U : Type) (P : U -> U -> Prop)
   (H : exists x : U, forall y : U, P x y) 
   (y : U) =>
 match H with
 | ex_intro _ x x0 =>
     (fun (x1 : U) (H0 : forall y0 : U, P x1 y0) =>
      ex_intro (fun x2 : U => P x2 y) x1 (H0 y)) x x0
 end)).
Defined.

Print sig_ind.
(* {x : A | P x} *)