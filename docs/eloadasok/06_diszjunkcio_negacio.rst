6. előadás: Diszjunkció és negáció
==================================

Az óra Coq-fájlja:
`6/diszjunkcio_negacio.v <https://github.com/mozow01/Matematikai-logika-VIK/blob/main/6/diszjunkcio_negacio.v>`_.
A részletesebb háttér a
`proofs_for_CS_students.pdf <https://github.com/mozow01/Matematikai-logika-VIK/blob/main/proofs_for_CS_students.pdf>`_
3–4. fejezete.

Diszjunkció
-----------

Egy ``A \/ B`` bizonyítás megmondja, hogy melyik oldalhoz van
bizonyításunk. A két bevezetési és az egy kiküszöbölési szabály:

.. math::

   \frac{\Gamma \vdash A}{\Gamma \vdash A \lor B}\;{\lor I_1}
   \qquad
   \frac{\Gamma \vdash B}{\Gamma \vdash A \lor B}\;{\lor I_2}

.. math::

   \frac{\Gamma \vdash A \lor B
         \qquad \Gamma,A \vdash C
         \qquad \Gamma,B \vdash C}
        {\Gamma \vdash C}\;{\lor E}

Kiküszöböléskor két esetet vizsgálunk, és mindkét esetben ugyanazt a ``C``
célt kell bizonyítani.

Coqban:

* ``left`` választja az ``A`` oldalt;
* ``right`` választja a ``B`` oldalt;
* ``destruct H as [HA | HB]`` választ esetet egy ``H : A \/ B``
  bizonyítás alapján.

.. code-block:: coq

   Lemma diszjunkcio_felcserel : forall A B : Prop,
     A \/ B -> B \/ A.
   Proof.
     intros A B H.
     destruct H as [HA | HB].
     - right. exact HA.
     - left. exact HB.
   Qed.

Hamis és negáció
----------------

A ``False`` típusnak nincs konstruktora. Ha mégis van ``False`` típusú
bizonyításunk, abból bármilyen állítás következik.

.. math::

   \frac{\Gamma \vdash \bot}{\Gamma \vdash A}\;{\bot E}

A negáció az implikáció rövidítése:

.. math::

   \neg A := A \to \bot.

Ezért egy ``~ A`` bizonyítás olyan program, amely egy ``A`` bizonyításából
ellentmondást készít. Coqban az ``unfold not`` megmutatja ezt az
``A -> False`` alakot, az ``exfalso`` pedig ``False``-ra cseréli a célt.

.. code-block:: coq

   Lemma tagado_kovetkeztetes : forall A B : Prop,
     (A -> B) -> ~ B -> ~ A.
   Proof.
     intros A B HAB HnB HA.
     apply HnB.
     apply HAB.
     exact HA.
   Qed.

Az ``A -> ~~ A`` irány bizonyítható. A ``~~ A -> A`` irány általában nem
bizonyítható intuicionista logikában.

De Morgan
---------

A diszjunkció tagadására vonatkozó azonosság feltétel nélkül bizonyítható:

.. math::

   \neg(A \lor B) \leftrightarrow (\neg A \land \neg B).

A konjunkció tagadásának egyik irányához el kell tudnunk dönteni legalább
``A``-t. A feltételt a tételben adjuk meg; nem használunk rejtett klasszikus
Coq-beállítást.

.. code-block:: coq

   Theorem de_morgan_es_eldontheto : forall A B : Prop,
     (A \/ ~ A) ->
     (~ (A /\ B) <-> (~ A \/ ~ B)).

Az implikáció jellemzése
------------------------

Ha ``A`` eldönthető, akkor az ``A -> B`` állítás a ``~ A \/ B`` alakkal
ekvivalens.

.. code-block:: coq

   Theorem implikacio_jellemzese_eldontheto : forall A B : Prop,
     (A \/ ~ A) ->
     ((A -> B) <-> (~ A \/ B)).

Az ``A \/ ~ A`` feltétel nélkül csak a ``(~ A \/ B) -> (A -> B)`` irány
bizonyítható. A másik irányban a feltétel alapján választunk ``A`` és
``~ A`` között.

1. gyakorló: diszjunkció
------------------------

Melyik levezetési szerkezet felel meg az alábbi Coq-bizonyításnak?

.. code-block:: coq

   Lemma vagy_felcserel_gyakorlo : forall A B : Prop,
     A \/ B -> B \/ A.
   Proof.
     intros A B H.
     destruct H as [HA | HB].
     - right. exact HA.
     - left. exact HB.
   Qed.

.. raw:: html

   <div data-lesson6-practice="disjunction-tree">
     <noscript>A gyakorló használatához engedélyezni kell a JavaScriptet.</noscript>
   </div>

2. gyakorló: kontrapozíció
--------------------------

Melyik levezetési szerkezet felel meg az alábbi Coq-bizonyításnak?

.. code-block:: coq

   Lemma kontrapozicio_gyakorlo : forall A B : Prop,
     (A -> B) -> ~ B -> ~ A.
   Proof.
     intros A B HAB HnB HA.
     apply HnB.
     apply HAB.
     exact HA.
   Qed.

.. raw:: html

   <div data-lesson6-practice="contraposition-tree">
     <noscript>A gyakorló használatához engedélyezni kell a JavaScriptet.</noscript>
   </div>

3. gyakorló: De Morgan
----------------------

Melyik levezetési szerkezet felel meg az alábbi Coq-bizonyításnak?

.. code-block:: coq

   Lemma de_morgan_bal_gyakorlo : forall A B : Prop,
     ~ (A \/ B) -> ~ A /\ ~ B.
   Proof.
     intros A B H.
     split.
     - intro HA. apply H. left. exact HA.
     - intro HB. apply H. right. exact HB.
   Qed.

.. raw:: html

   <div data-lesson6-practice="de-morgan-tree">
     <noscript>A gyakorló használatához engedélyezni kell a JavaScriptet.</noscript>
   </div>

4. gyakorló: az implikáció egyik iránya
----------------------------------------

Melyik levezetési szerkezet felel meg az alábbi Coq-bizonyításnak?

.. code-block:: coq

   Lemma implikacio_vagy_gyakorlo : forall A B : Prop,
     (A \/ ~ A) -> (A -> B) -> (~ A \/ B).
   Proof.
     intros A B Dontes HAB.
     destruct Dontes as [HA | HnA].
     - right. apply HAB. exact HA.
     - left. exact HnA.
   Qed.

.. raw:: html

   <div data-lesson6-practice="implication-tree">
     <noscript>A gyakorló használatához engedélyezni kell a JavaScriptet.</noscript>
   </div>
