7. előadás: Kvantorok bevezető
==============================

Az óra Coq-fájlja:
`7/kvantorok_alapok.v <https://github.com/mozow01/Matematikai-logika-VIK/blob/main/7/kvantorok_alapok.v>`_.
A részletesebb háttér a
`proofs_for_CS_students.pdf <https://github.com/mozow01/Matematikai-logika-VIK/blob/main/proofs_for_CS_students.pdf>`_
kvantorokról szóló része.

Predikátumok
------------

Egy ``P : U -> Prop`` predikátum minden ``x : U`` elemhez egy állítást
rendel. A ``P x`` állítás azt fejezi ki, hogy az ``x`` elem rendelkezik a
``P`` tulajdonsággal.

* ``forall x, P x``: minden ``x : U`` elemhez tudunk ``P x`` bizonyítást
  készíteni;
* ``exists x, P x``: van egy konkrét tanúnk, és van hozzá ``P x``
  bizonyításunk.

Univerzális kvantor
-------------------

Az univerzális kvantor bevezetési és kiküszöbölési szabálya:

.. math::

   \frac{x:U,\,\Gamma \vdash P(x)}
        {\Gamma \vdash \forall x:U.\,P(x)}\;{\forall I}
   \qquad
   \frac{\Gamma \vdash \forall x:U.\,P(x)}
        {\Gamma \vdash P(t)}\;{\forall E}

A ``forall`` bevezetésekor ``x`` tetszőleges és friss. Nem használhatunk
róla olyan külön feltételt, amely más elemekre nem igaz. Kiküszöböléskor az
általános állítást egy konkrét ``t`` elemre alkalmazzuk.

Coqban:

* ``intro x`` bevezet egy tetszőleges elemet;
* ``apply H`` vagy ``exact (H t)`` specializálja a
  ``H : forall x, P x`` feltételt.

.. code-block:: coq

   Lemma minden_pontonkent : forall (U : Type) (P Q : U -> Prop),
     (forall x, P x -> Q x) ->
     (forall x, P x) ->
     forall x, Q x.
   Proof.
     intros U P Q HPQ HP x.
     apply HPQ.
     apply HP.
   Qed.

Egzisztenciális kvantor
-----------------------

Az egzisztenciális kvantor bevezetési és kiküszöbölési szabálya:

.. math::

   \frac{\Gamma \vdash P(t)}
        {\Gamma \vdash \exists x:U.\,P(x)}\;{\exists I}

.. math::

   \frac{\Gamma \vdash \exists x:U.\,P(x)
         \qquad a:U,\,P(a),\,\Gamma \vdash C}
        {\Gamma \vdash C}\;{\exists E}

Bevezetéskor meg kell adni a tanút. Kiküszöböléskor egy friss néven
kibontjuk az ismeretlen tanút és a hozzá tartozó bizonyítást. A végső cél
nem függhet attól, pontosan melyik tanút kaptuk.

Coqban:

* ``exists t`` a ``t`` tanút választja;
* ``destruct H as [x HPx]`` kibontja a tanút és a bizonyítást.

.. code-block:: coq

   Lemma letezik_kep : forall (U : Type) (P Q : U -> Prop),
     (forall x, P x -> Q x) ->
     (exists x, P x) ->
     exists x, Q x.
   Proof.
     intros U P Q HPQ HP.
     destruct HP as [x HPx].
     exists x.
     apply HPQ.
     exact HPx.
   Qed.

A kvantorok sorrendje
---------------------

A két alábbi állítás nem ugyanaz:

.. math::

   \forall x\,\exists y\,R(x,y)
   \qquad\text{és}\qquad
   \exists y\,\forall x\,R(x,y).

Az elsőben a ``y`` tanú függhet ``x``-től. A második egyetlen közös tanút
kér minden ``x``-hez. Ezért a közös tanút adó irányból következik a másik:

.. code-block:: coq

   Theorem egy_tanu_mindenre : forall
       (U V : Type) (R : U -> V -> Prop),
     (exists x, forall y, R x y) ->
     forall y, exists x, R x y.

1. gyakorló: univerzális kvantor
--------------------------------

Mindhárom program helyes és ugyanazt az állítást bizonyítja. Válassza ki
azt, amelyik az alábbi levezetési sorrendet követi:

.. code-block:: text

   →I: a konjunkciós feltétel bevezetése
   ∨I₂: a diszjunkció jobb oldalának választása
   ∀I: egy friss a elem bevezetése
   ∧E₁, majd ∀E: P a kinyerése a feltételből

.. code-block:: coq

   Lemma minden_fa_gyakorlo : forall (U : Type) (P Q : U -> Prop),
     ((forall x, P x) /\ (forall x, Q x)) ->
     (forall x, Q x) \/ (forall x, P x).

.. raw:: html

   <div data-lesson7-practice="forall-program">
     <noscript>A gyakorló használatához engedélyezni kell a JavaScriptet.</noscript>
   </div>

2. gyakorló: egzisztenciális kvantor
------------------------------------

Mindhárom program helyes és ugyanazt az állítást bizonyítja. Válassza ki
azt, amelyik az alábbi levezetési sorrendet követi:

.. code-block:: text

   →I: az egzisztenciális feltétel bevezetése
   ∃E: az a tanú és a Ha bizonyítás kibontása
   ∨I₂: a diszjunkció jobb oldalának választása
   ∃I: az a tanú újbóli becsomagolása
   ∧E₁: P a kinyerése Ha-ból

.. code-block:: coq

   Lemma letezik_fa_gyakorlo : forall (U : Type) (P Q : U -> Prop),
     (exists x, P x /\ Q x) ->
     (exists x, Q x) \/ (exists x, P x).

.. raw:: html

   <div data-lesson7-practice="exists-program">
     <noscript>A gyakorló használatához engedélyezni kell a JavaScriptet.</noscript>
   </div>
