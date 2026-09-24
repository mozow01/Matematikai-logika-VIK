(* A masodik oran bevezetett Boole nyelv, denotacio es Prg tipus. *)
Load "2/ite".


(* ====================================================== *)
(*                       Helyesseg                        *)
(* ====================================================== *)

(* A kontextus igaz, ha minden benne szereplo tipus
   denotacioja igaz. *)
Definition true_context (G : list Boole) : Prop :=
  forall A,
    In A G ->
    denote A = true.


(* Ha igaz kontextusbol irtunk A tipusu programot,
   akkor A denotacioja igaz. *)
Theorem soundness_general :
  forall G A,
    Prg G A ->
    true_context G ->
    denote A = true.
Proof.
  intros G A p.
  induction p; intro HG.

  (* vz *)
  - apply HG.
    simpl.
    auto.

  (* vs *)
  - apply IHp.
    intros X HX.
    apply HG.
    simpl.
    auto.

  (* tt *)
  - reflexivity.

  (* abs *)
  - apply IHp in HG.
    discriminate HG.

  (* iteI *)
  - simpl.
    destruct (denote A) eqn:HA.

    (* A igaz, tehat a B-ag kovetkezik. *)
    + apply IHp1.
      intros X [HX | HX].

      * subst.
        exact HA.

      * apply HG.
        exact HX.

    (* A hamis, tehat a C-ag kovetkezik. *)
    + apply IHp2.
      intros X [HX | HX].

      * subst.
        unfold Neg.
        simpl.
        rewrite HA.
        reflexivity.

      * apply HG.
        exact HX.

  (* iteTru *)
  - apply IHp1 in HG as Hite.
    apply IHp2 in HG as HA.

    simpl in Hite.
    rewrite HA in Hite.

    exact Hite.

  (* iteFal *)
  - apply IHp1 in HG as Hite.
    apply IHp2 in HG as Hneg.

    unfold Neg in Hneg.
    simpl in Hneg.

    destruct (denote A) eqn:HA.

    + discriminate Hneg.

    + simpl in Hite.
      rewrite HA in Hite.
      exact Hite.

  (* iteSame *)
  - apply IHp in HG.

    simpl in HG.
    destruct (denote A).

    + exact HG.

    + exact HG.
Qed.


(* Ures kontextusban nincs kulon szemantikai feltetel. *)
Theorem soundness :
  forall A,
    inhabited (Prg [] A) ->
    denote A = true.
Proof.
  intros A [p].

  apply (soundness_general [] A p).

  intros X HX.
  inversion HX.
Qed.


(* ====================================================== *)
(*                       Teljesseg                        *)
(* ====================================================== *)

(* Ha A igaz, akkor A programjat allitjuk elo.
   Ha A hamis, akkor Neg A programjat allitjuk elo. *)
Theorem complete_by_value :
  forall A,
    match denote A with
    | true  => Prg [] A
    | false => Prg [] (Neg A)
    end.
Proof.
  induction A as [| |A IHA B IHB C IHC].

  (* Tru *)
  - apply tt.

  (* Fal: Neg Fal levezetheto. *)
  - unfold Neg.
    apply iteI.

    + apply vz.

    + apply tt.

  (* Ite A B C *)
  - simpl.
    destruct (denote A) eqn:HA;
      simpl in IHA.

    (* A igaz, ezert B erteke dont. *)
    + destruct (denote B) eqn:HB;
        simpl in IHB.

      (* B igaz, ezert Ite A B C igaz. *)
      * apply iteI.

        (* A feltetelezese mellett B levezetheto. *)
        -- apply weakening.
           exact IHB.

        (* Neg A feltetelezese ellentmond A-nak. *)
        -- apply abs.
           apply (@contradictionI _ A).

           ++ apply weakening.
              exact IHA.

           ++ apply vz.

      (* B hamis, ezert Neg (Ite A B C) igaz. *)
      * unfold Neg.
        apply iteI.

        (* Ite A B C es A alapjan B kovetkezik,
           de Neg B is levezetheto. *)
        -- apply (@contradictionI _ B).

           ++ apply iteTru with
                (A := A)
                (C := C).

              ** apply vz.

              ** apply weakening.
                 exact IHA.

           ++ apply weakening.
              exact IHB.

        -- apply tt.

    (* A hamis, ezert C erteke dont. *)
    + destruct (denote C) eqn:HC;
        simpl in IHC.

      (* C igaz, ezert Ite A B C igaz. *)
      * apply iteI.

        (* A feltetelezese ellentmond Neg A-nak. *)
        -- apply abs.
           apply (@contradictionI _ A).

           ++ apply vz.

           ++ apply weakening.
              exact IHA.

        (* Neg A feltetelezese mellett C levezetheto. *)
        -- apply weakening.
           exact IHC.

      (* C hamis, ezert Neg (Ite A B C) igaz. *)
      * unfold Neg.
        apply iteI.

        (* Ite A B C es Neg A alapjan C kovetkezik,
           de Neg C is levezetheto. *)
        -- apply (@contradictionI _ C).

           ++ apply iteFal with
                (A := A)
                (B := B).

              ** apply vz.

              ** apply weakening.
                 exact IHA.

           ++ apply weakening.
              exact IHC.

        -- apply tt.
Qed.


(* A complete_by_value eredmenyebol kivesszuk
   az igaz esethez tartozo programot. *)
Lemma take_true_program :
  forall A,
    (match denote A with
     | true  => Prg [] A
     | false => Prg [] (Neg A)
     end) ->
    denote A = true ->
    Prg [] A.
Proof.
  intros A p HA.

  rewrite HA in p.

  exact p.
Qed.


Theorem completeness :
  forall A,
    denote A = true ->
    inhabited (Prg [] A).
Proof.
  intros A HA.

  constructor.

  apply take_true_program with (A := A).

  - apply complete_by_value.

  - exact HA.
Qed.


(* ====================================================== *)
(*              Helyesseg es teljesseg egyben             *)
(* ====================================================== *)

Theorem soundness_and_completeness :
  forall A,
    inhabited (Prg [] A) <->
    denote A = true.
Proof.
  intro A.
  split.

  - apply soundness.

  - apply completeness.
Qed.
