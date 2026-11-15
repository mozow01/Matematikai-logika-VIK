8. előadás: Kvantorok folytatás és prenex alak
================================================

Az óra Coq-fájlja:
`8/prenex_implikacio.v <https://github.com/mozow01/Matematikai-logika-VIK/blob/main/8/prenex_implikacio.v>`_.

Kvantorok sorrendje
-------------------

Az ``exists x, forall y, R x y`` állítás egyetlen ``x`` tanút ad, amely
minden ``y`` esetén használható. Ezért bizonyítható:

.. code-block:: coq

   Theorem egy_tanu_mindenre : forall
       (U V : Type) (R : U -> V -> Prop),
     (exists x, forall y, R x y) ->
     forall y, exists x, R x y.

A fordított irány általában nem igaz. A ``forall y, exists x, R x y``
állításban a választott ``x`` függhet ``y``-tól.

Negáció és kvantorok
--------------------

Az alábbi azonosság intuicionista logikában is mindkét irányban
bizonyítható:

.. math::

   \neg\exists x\,A(x)
   \quad\leftrightarrow\quad
   \forall x\,\neg A(x).

Balról jobbra egy feltételezett ``A x`` bizonyításból egzisztenciális tanút
építünk, ami ellentmond a kiinduló feltételnek. Jobbról balra kibontjuk a
feltételezett egzisztenciális tanút, majd alkalmazzuk rá az általános
tagadást.

.. code-block:: coq

   Theorem nem_letezik_azonossag : forall
       (U : Type) (A : U -> Prop),
     (~ exists x, A x) <-> forall x, ~ A x.

Az ``(exists x, ~ A x) -> ~ (forall x, A x)`` irány szintén bizonyítható. A
fordított irányhoz általában további klasszikus feltétel kell.

Prenex alak
-----------

Prenex alakban a kvantorok a formula elején állnak. Ezen az órán csak az
implikáció négy alaphelyzetét vizsgáljuk. ``B : Prop`` nem függ ``x``-től,
míg ``A : U -> Prop`` igen.

.. list-table::
   :header-rows: 1

   * - Kiinduló alak
     - Kvantor elöl
     - Feltétel
   * - ``B -> forall x, A x``
     - ``forall x, B -> A x``
     - egyik irányhoz sem kell további feltétel
   * - ``(exists x, A x) -> B``
     - ``forall x, A x -> B``
     - egyik irányhoz sem kell további feltétel
   * - ``B -> exists x, A x``
     - ``exists x, B -> A x``
     - a nehezebb irányhoz nem üres ``U`` és ``B \/ ~ B`` kell
   * - ``(forall x, A x) -> B``
     - ``exists x, A x -> B``
     - a nehezebb irányhoz nem üres ``U`` és döntési feltétel kell

Az első két eset intuicionista
------------------------------

Az univerzális kvantor az implikáció jobb oldaláról feltétel nélkül
kivihető:

.. code-block:: coq

   Theorem prenex_minden_jobbra : forall
       (U : Type) (A : U -> Prop) (B : Prop),
     ((B -> forall x, A x) <-> forall x, B -> A x).

Az egzisztenciális kvantor az implikáció bal oldaláról szintén feltétel
nélkül kivihető:

.. code-block:: coq

   Theorem prenex_letezik_balra : forall
       (U : Type) (A : U -> Prop) (B : Prop),
     (((exists x, A x) -> B) <-> forall x, A x -> B).

A másik két eset feltételei
---------------------------

A ``B -> exists x, A x`` alakból akkor is tanút kell választani, ha ``B``
hamis. Ezért a tételben külön bemenetként szerepel:

* ``exists x : U, True``: az alaphalmaz nem üres;
* ``B \/ ~ B``: eldönthető, hogy ``B`` fennáll-e.

A ``(forall x, A x) -> B`` esetben is tanút kell választani. A használt
döntési feltétel:

.. code-block:: coq

   (forall x, A x) \/ exists x, ~ A x

Nem töltünk be klasszikus Coq-könyvtárat. Minden szükséges feltétel látható
a tétel állításában.

Gyakorló: három program és három levezetés
------------------------------------------

Mindhárom program helyes, és ugyanazt az állítást bizonyítja. A különbség
az, hogy az egzisztenciális feltételt a két univerzális változó bevezetése
előtt, közöttük vagy után bontják ki.

.. code-block:: coq

   Lemma kvantor_sorrend_A : forall
       (U V W : Type) (R : U -> V -> W -> Prop),
     (exists x, forall y z, R x y z) ->
     forall z y, exists x, R x y z.
   Proof.
     intros U V W R H.
     destruct H as [x Hx].
     intros z y.
     exists x.
     apply Hx.
   Qed.

   Lemma kvantor_sorrend_B : forall
       (U V W : Type) (R : U -> V -> W -> Prop),
     (exists x, forall y z, R x y z) ->
     forall z y, exists x, R x y z.
   Proof.
     intros U V W R H z.
     destruct H as [x Hx].
     intro y.
     exists x.
     apply Hx.
   Qed.

   Lemma kvantor_sorrend_C : forall
       (U V W : Type) (R : U -> V -> W -> Prop),
     (exists x, forall y z, R x y z) ->
     forall z y, exists x, R x y z.
   Proof.
     intros U V W R H z y.
     destruct H as [x Hx].
     exists x.
     apply Hx.
   Qed.

Párosítsa a programokat a levezetés külső szabályainak sorrendjével.
Mindegyik programot pontosan egyszer kell felhasználni.

.. raw:: html

   <div data-lesson8-practice="quantifier-matching">
     <noscript>A gyakorló használatához engedélyezni kell a JavaScriptet.</noscript>
   </div>
