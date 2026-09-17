2. óra: Programok mint tanúsítványok
====================================

Ezen az órán átlépünk a nyelv második szintjére. Az első órán
``Boole``-kifejezéseket, vagyis a tárgynyelv lehetséges **típusait** és
**állításait** építettük. Most adott tárgynyelvi típushoz **programokat**
fogunk írni. Egy ilyen program egyben ellenőrizhető tanúsítvány: azt
igazolja, hogy a típusa által leírt állítás levezethető.

A bemelegítő feladatok a
`1/ite.v <https://github.com/mozow01/Matematikai-logika-VIK/blob/main/1/ite.v>`_
``denote`` és ``beta_reduce`` definícióit használják; helyi munka közben
ezeket az első órai fájl aljára írd. Az új ``prg``-anyag szerkeszthető
alapfájlja már a
`2/prg.v <https://github.com/mozow01/Matematikai-logika-VIK/blob/main/2/prg.v>`_.

Bemelegítés: az ITE 4×4 feladatbank
-----------------------------------

Az alábbi tizenhat feladat ugyanaz a négy kategória, kategóriánként négy
variánssal, amelyből a Moodle **mind a négy kategóriából egy-egy** véletlen
kérdést választ. Itt mindegyiket külön jsCoq-ablakban lehet kipróbálni. A
négy pozíció így összesen :math:`4^4=256` különböző feladatsort adhat. A
sorrend szándékos:

1. először kiértékelési útvonalakat követünk;
2. utána logikai műveletek jelentését igazoljuk;
3. denotációs azonosságokat bizonyítunk;
4. végül egyszerre beszélünk szintaktikai különbözőségről és azonos
   jelentésről.

Az ablakban léptess a ``Proof.`` sorig. Ott nyitott bizonyítási cél vár:
írd a komment helyére a taktikáidat, végül zárd a bizonyítást ``Qed.``-del.

.. important::

   Ezekhez a feladatokhoz nem kell a normalizációs vagy a ``denote_beta``
   tétel. Elég az ``intros``, ``simpl``, ``unfold``, ``rewrite``,
   ``destruct``, ``split``, ``discriminate`` és ``reflexivity``.

.. note::

   Minden megnyitott ablak külön jsCoq-motort indít. Érdemes egyszerre csak
   egy-két feladattal dolgozni; az oldal újratöltése bezárja a motorokat.

1. csoport: háromszintű béta-redukció
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Mind a négy feladatban belülről kifelé kell megállapítani, hogy az egymásba
ágyazott feltételek melyik ágat választják. A hipotéziseket érdemes névvel
bevezetni, majd a ``simpl`` után ezekkel átírni a célt.

1/A – ``Tru / Tru / Tru``
^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block:: coq

   Theorem beta_nested_ttt :
     forall A B C D E F G,
       beta_reduce A = Tru ->
       beta_reduce B = Tru ->
       beta_reduce D = Tru ->
       beta_reduce (Ite (Ite (Ite A B C) D E) F G) = beta_reduce F.

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=practice_beta_1"
     title="ITE 4x4: háromszintű béta-redukció, Tru Tru Tru"
     loading="lazy" allow="clipboard-write"></iframe>

1/B – ``Tru / Fal / Fal``
^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block:: coq

   Theorem beta_nested_tff :
     forall A B C D E F G,
       beta_reduce A = Tru ->
       beta_reduce B = Fal ->
       beta_reduce E = Fal ->
       beta_reduce (Ite (Ite (Ite A B C) D E) F G) = beta_reduce G.

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=practice_beta_2"
     title="ITE 4x4: háromszintű béta-redukció, Tru Fal Fal"
     loading="lazy" allow="clipboard-write"></iframe>

1/C – ``Fal / Tru / Fal``
^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block:: coq

   Theorem beta_nested_ftf :
     forall A B C D E F G,
       beta_reduce A = Fal ->
       beta_reduce C = Tru ->
       beta_reduce D = Fal ->
       beta_reduce (Ite (Ite (Ite A B C) D E) F G) = beta_reduce G.

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=practice_beta_3"
     title="ITE 4x4: háromszintű béta-redukció, Fal Tru Fal"
     loading="lazy" allow="clipboard-write"></iframe>

1/D – ``Fal / Fal / Tru``
^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block:: coq

   Theorem beta_nested_fft :
     forall A B C D E F G,
       beta_reduce A = Fal ->
       beta_reduce C = Fal ->
       beta_reduce E = Tru ->
       beta_reduce (Ite (Ite (Ite A B C) D E) F G) = beta_reduce F.

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=practice_beta_4"
     title="ITE 4x4: háromszintű béta-redukció, Fal Fal Tru"
     loading="lazy" allow="clipboard-write"></iframe>

2. csoport: származtatott műveletek denotációja
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Most egy-egy ``Ite``-kódolásról kell megmutatni, hogy ugyanazt az
igazságfüggvényt jelenti, mint a Coq megfelelő ``bool``-művelete. Itt nem a
két szintaxisfa egyenlőségét, hanem a denotációk egyenlőségét bizonyítjuk.

2/A – Diszjunkció
^^^^^^^^^^^^^^^^^

.. code-block:: coq

   Theorem ite_or_denote :
     forall A B,
       denote (Ite A Tru B) = orb (denote A) (denote B).

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=practice_connective_1"
     title="ITE 4x4: diszjunkció denotációja"
     loading="lazy" allow="clipboard-write"></iframe>

2/B – Implikáció
^^^^^^^^^^^^^^^^

.. code-block:: coq

   Theorem ite_imp_denote :
     forall A B,
       denote (Ite A B Tru) =
       orb (negb (denote A)) (denote B).

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=practice_connective_2"
     title="ITE 4x4: implikáció denotációja"
     loading="lazy" allow="clipboard-write"></iframe>

2/C – Kizáró vagy
^^^^^^^^^^^^^^^^^

.. code-block:: coq

   Theorem ite_xor_denote :
     forall A B,
       denote (Ite A (Neg B) B) = xorb (denote A) (denote B).

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=practice_connective_3"
     title="ITE 4x4: kizáró vagy denotációja"
     loading="lazy" allow="clipboard-write"></iframe>

2/D – Ekvivalencia
^^^^^^^^^^^^^^^^^^

.. code-block:: coq

   Theorem ite_eqv_denote :
     forall A B,
       denote (Ite A B (Neg B)) =
       Bool.eqb (denote A) (denote B).

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=practice_connective_4"
     title="ITE 4x4: ekvivalencia denotációja"
     loading="lazy" allow="clipboard-write"></iframe>

3. csoport: denotációs azonosságok
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Ezek a tételek általános ``Boole``-kifejezésekről szólnak. A változókat nem
lehet közvetlenül ``Tru`` és ``Fal`` esetekre bontani, mert az ``Ite`` is
``Boole`` konstruktor. A ``denote A : bool`` értéke viszont valóban kétféle;
ezért többnyire azon érdemes esetbontást végezni.

3/A – Kettős negáció
^^^^^^^^^^^^^^^^^^^^

.. code-block:: coq

   Theorem double_neg_denote :
     forall A,
       denote (Neg (Neg A)) = denote A.

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=practice_denotation_1"
     title="ITE 4x4: kettős negáció denotációja"
     loading="lazy" allow="clipboard-write"></iframe>

3/B – A konjunkció kommutativitása
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block:: coq

   Theorem and2_comm_denote :
     forall A B,
       denote (And2 A B) = denote (And2 B A).

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=practice_denotation_2"
     title="ITE 4x4: a konjunkció denotációs kommutativitása"
     loading="lazy" allow="clipboard-write"></iframe>

3/C – A konjunkció asszociativitása
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block:: coq

   Theorem and2_assoc_denote :
     forall A B C,
       denote (And2 (And2 A B) C) =
       denote (And2 A (And2 B C)).

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=practice_denotation_3"
     title="ITE 4x4: a konjunkció denotációs asszociativitása"
     loading="lazy" allow="clipboard-write"></iframe>

3/D – De Morgan-azonosság
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block:: coq

   Theorem de_morgan_denote :
     forall A B,
       denote (Neg (And2 A B)) =
       denote (Ite (Neg A) Tru (Neg B)).

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=practice_denotation_4"
     title="ITE 4x4: De Morgan-azonosság denotációval"
     loading="lazy" allow="clipboard-write"></iframe>

4. csoport: szintaxis és szemantika
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Minden állítás egy konjunkció. Az első fele azt mondja ki, hogy két
kifejezés **nem ugyanaz a szintaxisfa**; ezt a konstruktorok különbözősége
adja. A második fele azt mondja ki, hogy a két kifejezésnek mégis **azonos a
denotációja**. A ``split`` után ezért a két részcél egészen más módszert kér.

4/A – Azonos igaz ágak
^^^^^^^^^^^^^^^^^^^^^^

.. code-block:: coq

   Theorem same_true_branches :
     forall A,
       Ite A Tru Tru <> Tru /\
       denote (Ite A Tru Tru) = denote Tru.

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=practice_syntax_1"
     title="ITE 4x4: azonos igaz ágak"
     loading="lazy" allow="clipboard-write"></iframe>

4/B – Beágyazott állandó igaz
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block:: coq

   Theorem nested_true_branches :
     forall A B,
       Ite A (Ite B Tru Tru) Tru <> Tru /\
       denote (Ite A (Ite B Tru Tru) Tru) = denote Tru.

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=practice_syntax_2"
     title="ITE 4x4: beágyazott állandó igaz"
     loading="lazy" allow="clipboard-write"></iframe>

4/C – Beágyazott állandó hamis
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block:: coq

   Theorem nested_false_branches :
     forall A B,
       Ite A (Ite B Fal Fal) Fal <> Fal /\
       denote (Ite A (Ite B Fal Fal) Fal) = denote Fal.

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=practice_syntax_3"
     title="ITE 4x4: beágyazott állandó hamis"
     loading="lazy" allow="clipboard-write"></iframe>

4/D – Beágyazott konjunkció, állandó hamis
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code-block:: coq

   Theorem nested_and_false :
     forall A B,
       And2 A (And2 B Fal) <> Fal /\
       denote (And2 A (And2 B Fal)) = denote Fal.

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=practice_syntax_4"
     title="ITE 4x4: beágyazott konjunkció, állandó hamis"
     loading="lazy" allow="clipboard-write"></iframe>

Új anyag: belépés Boole falvaiba
--------------------------------

Képzeljük el, hogy minden ``A : Boole`` kifejezés egy külön falu neve. A
falu kapuján nem az léphet be, aki egyszerűen azt mondja, hogy ``A`` igaz.
Fel kell mutatnia egy, a szabályok szerint kiállított **útlevelet**.

.. raw:: html

   <div class="concept-grid">
     <section class="concept-card">
       <h3>Úti cél</h3>
       <p><code>A : Boole</code></p>
       <p>A tárgynyelvi állítás, illetve típus neve: ennek a falujába szeretnénk belépni.</p>
     </section>
     <section class="concept-card">
       <h3>Iratmappa</h3>
       <p><code>G : list Boole</code></p>
       <p>A már rendelkezésünkre álló feltevések listája.</p>
     </section>
     <section class="concept-card">
       <h3>Útlevél</h3>
       <p><code>p : prg G A</code></p>
       <p>Ellenőrizhető program, amely a <code>G</code> irataiból tanúsítja <code>A</code>-t.</p>
     </section>
   </div>

A Coq típusellenőrzője a határőr. Nem fogad el szóbeli ígéretet: csak olyan
``p`` programot, amelynek ténylegesen ``prg G A`` a típusa. Így ugyanaz az
objektum egyszerre

* a Coq által ellenőrizhető, szerkezetes **program**;
* egy állítás **bizonyítása**;
* és a bizonyítás helyességét igazoló **tanúsítvány**.

Ezt a megfelelést nevezik Curry--Howard-megfelelésnek. Ezen az órán ennek
egy apró, teljesen kézzel követhető változatát építjük fel.

Fontos a két szintet külön tartani. Az ``A : Boole`` Coq-beli adat, amely a
**tárgynyelvben** képvisel egy típust vagy állítást. A tanúsítvány tényleges
Coq-típusa ``prg G A : Type``; ennek fogjuk egy ``p`` lakóját megírni.

A ``prg G A`` ítélet
--------------------

A papíron használt

.. math::

   \Gamma \vdash A

ítélet Coq-beli alakja ``prg G A``. Olvasata: „a ``G`` kontextus
feltevéseiből van ``A`` típusú programunk”. A kontextust listával ábrázoljuk:

.. code-block:: coq

   []                 (* üres kontextus *)
   [A]                (* egy feltevés *)
   B :: A :: G        (* B, majd A, majd G feltevései *)

A lista feje a legfrissebb feltevés. Az ``A :: G`` tehát nem egy logikai
konjunkció: azt jelenti, hogy ``G`` elé még felvettük ``A``-t.

.. warning::

   A ``prg G A`` nem azt számolja ki, hogy ``denote A`` igaz-e. Új típust
   ad meg: azoknak a tanúsítványoknak a típusát, amelyeket az alábbi
   konstruktorok valamelyikével szabályosan fel tudunk építeni.

A programnyelv definíciója
--------------------------

.. code-block:: coq

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
       prg (A :: G) B ->
       prg (Neg A :: G) C ->
       prg G (Ite A B C)

   | iteTru : forall (G : list Boole) (A B C : Boole),
       prg G (Ite A B C) -> prg G A -> prg G B

   | iteFal : forall (G : list Boole) (A B C : Boole),
       prg G (Ite A B C) -> prg G (Neg A) -> prg G C

   | iteSame : forall (G : list Boole) (A D : Boole),
       prg G (Ite A D D) -> prg G D.

A ``prg`` két indexet kap: a ``G`` kontextust és az ``A`` célt. A
konstruktorok nem új állításokat hoznak létre, hanem pontosan meghatározzák,
milyen alakú útlevelet fogad el a típusellenőrző.

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=prg_passports"
     title="A prg típus és az útlevél-hasonlat interaktív Coq-példája"
     loading="lazy" allow="clipboard-write"></iframe>

A nyolc útlevél-kiállítási szabály
----------------------------------

``vz`` – a legelső feltevés
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. math::

   \frac{}{A,\Gamma\vdash A}

Ha ``A`` ott van a kontextus fején, akkor közvetlenül felhasználhatjuk:

.. code-block:: coq

   vz G A : prg (A :: G) A

Az iratmappában legfelül fekvő ``A`` az igazoló irat; a ``vz G A``
felhasználásával ebből állítjuk ki a ``prg (A :: G) A`` útlevelet.

``vs`` – egy nem használt feltevés hozzáadása
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. math::

   \frac{\Gamma\vdash A}{B,\Gamma\vdash A}

Ha már van ``A``-útlevelünk, egy új ``B`` irat felvétele nem érvényteleníti:

.. code-block:: coq

   vs G A B : prg G A -> prg (B :: G) A

Ezt strukturális gyengítésnek nevezzük. A ``B`` feltevést nem kötelező
használni.

``tt`` – az igazság mindig elérhető
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. math::

   \frac{}{\Gamma\vdash \mathsf{Tru}}

A ``Tru`` típushoz semmilyen feltevés nem kell:

.. code-block:: coq

   tt G : prg G Tru

Ez az útlevél minden iratmappa mellett automatikusan kiállítható.

``abs`` – hamisságból bármi
~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. math::

   \frac{\Gamma\vdash \mathsf{Fal}}{\Gamma\vdash A}

Ha a kontextusból már ``Fal``-hoz jutottunk, akkor tetszőleges ``A``-hoz
készíthetünk programot:

.. code-block:: coq

   abs G A : prg G Fal -> prg G A

Ez az *ex falso quodlibet* szabály. A kép szerint egy ellentmondó iratmappa
után a rendszerben bármely úti cél tanúsítható.

``iteI`` – útlevél két lehetséges ágból
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. math::

   \frac{A,\Gamma\vdash B \qquad \neg A,\Gamma\vdash C}
        {\Gamma\vdash \mathsf{Ite}\;A\;B\;C}

Két ellenőrzött tervet kell adnunk:

* ha ``A`` rendelkezésre áll, tudjunk ``B``-t készíteni;
* ha ``Neg A`` rendelkezésre áll, tudjunk ``C``-t készíteni.

Ekkor a külső kontextusban tanúsítottuk az ``Ite A B C`` típust. Ez az
``Ite`` bevezetési szabálya.

``iteTru`` – a valódi ág használata
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. math::

   \frac{\Gamma\vdash \mathsf{Ite}\;A\;B\;C \qquad \Gamma\vdash A}
        {\Gamma\vdash B}

Ha van útlevelünk a teljes feltételeshez és külön tanúsítjuk a feltételt,
akkor megkapjuk a ``B`` ághoz tartozó útlevelet.

``iteFal`` – a hamis ág használata
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. math::

   \frac{\Gamma\vdash \mathsf{Ite}\;A\;B\;C \qquad \Gamma\vdash \neg A}
        {\Gamma\vdash C}

Ha a feltétel negációját tanúsítjuk, a ``C`` ág lép életbe.

``iteSame`` – azonos ágak elhagyása
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. math::

   \frac{\Gamma\vdash \mathsf{Ite}\;A\;D\;D}{\Gamma\vdash D}

Ha mindkét ág ``D``, akkor a feltétel értékétől függetlenül ``D`` a
használható eredmény.

Az alábbi ablakban mind a nyolc konstruktor típusát és néhány apró
útlevelet lehet lépésenként megvizsgálni.

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=prg_rules"
     title="A prg nyolc konstruktorának interaktív Coq-példái"
     loading="lazy" allow="clipboard-write"></iframe>

Első összetett program: ``weakening``
-------------------------------------

A gyengítést kényelmes névvel is ellátjuk:

.. code-block:: coq

   Definition weakening
     {G : list Boole} {A B : Boole}
     (I : prg G A) : prg (B :: G) A :=
     vs G A B I.

A kapcsos zárójelek implicit argumentumokat jelölnek. A híváskor a Coq
többnyire kiolvassa ``I`` típusából, mi ``G`` és ``A``; a cél típusából pedig
azt, mi ``B``. Ha mégsem, név szerint is megadhatjuk:

.. code-block:: coq

   weakening (B := C) i

Ha ``i : prg G A``, ennek típusa ``prg (C :: G) A``. A program nem nyúl
``C``-hez: csak megőrzi a régi útlevelet egy vastagabb iratmappában.

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=weakening"
     title="A weakening program interaktív Coq-példája"
     loading="lazy" allow="clipboard-write"></iframe>

Ellentmondás készítése: ``contradictionI``
------------------------------------------

Tegyük fel, hogy ugyanabban a ``G`` kontextusban van

.. code-block:: coq

   a  : prg G A
   na : prg G (Neg A)

A ``Neg A`` definíció szerint ``Ite A Fal Tru``. Ez tehát egy feltételes
program, amelynek igaz ága ``Fal``. Az ``iteTru`` szabály a ``na``
feltételes útlevél és az ``a`` feltétel együttese alapján pontosan ezt az
ágat adja:

.. code-block:: coq

   Definition contradictionI
     {G : list Boole} {A : Boole}
     (a : prg G A) (na : prg G (Neg A)) : prg G Fal :=
     iteTru G A Fal Tru na a.

A paraméterek az ``iteTru``-t erre a konkrét példányra állítják:

.. code-block:: text

   Ite A B   C   = Ite A Fal Tru = Neg A
         ^   ^
         |   |
         B   C

Az eredmény így ``prg G Fal``: szabályosan előállítottuk az ellentmondás
tanúsítványát.

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=contradiction"
     title="A contradictionI program interaktív Coq-példája"
     loading="lazy" allow="clipboard-write"></iframe>

Konjunkció bevezetése: ``andI``
-------------------------------

Most tegyük fel, hogy ugyanabban a kontextusban van egy ``A``- és egy
``B``-tanúsítványunk:

.. code-block:: coq

   a : prg G A
   b : prg G B

A cél ``prg G (And2 A B)``. Az ``And2 A B`` definíciója ``Ite A B Fal``,
ezért az ``iteI`` szabály pontosan két részfeladatot ad:

.. math::

   \frac{A,\Gamma\vdash B \qquad \neg A,\Gamma\vdash \mathsf{Fal}}
        {\Gamma\vdash \mathsf{Ite}\;A\;B\;\mathsf{Fal}}.

Az első ágban a régi ``b`` programot gyengítjük az új ``A`` feltevéssel. A
második ágban

* ``a``-t gyengítjük az új ``Neg A`` feltevéssel;
* ``vz`` segítségével kiolvassuk a kontextus fejéről ``Neg A``-t;
* a kettőből ``contradictionI`` előállítja ``Fal``-t.

.. code-block:: coq

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

A ``Defined.`` itt azt hangsúlyozza, hogy valóban programot építettünk: a
testét a Coq később is ki tudja bontani. A bizonyítási mód parancsai csak
kényelmesen megszerkesztik ugyanazt a programot, amelyet egyetlen hosszú
kifejezésként is megadhatnánk.

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=and_intro"
     title="Az andI program interaktív Coq-bizonyítása"
     loading="lazy" allow="clipboard-write"></iframe>

Mit vigyünk magunkkal?
----------------------

1. A ``Boole`` kifejezések most típusok, illetve állítások szerepét kapják.
2. Egy ``p : prg G A`` program ellenőrizhető tanúsítvány arra, hogy ``G``
   feltevéseiből elérhető ``A``.
3. A ``prg`` konstruktorai a megengedett bizonyítási szabályok.
4. A ``vz`` feltevést használ, a ``vs`` új, akár felesleges feltevést enged
   be, a ``tt`` feltétel nélkül tanúsítja ``Tru``-t, az ``abs`` pedig
   ``Fal``-ból bármit előállít.
5. Az ``iteI`` két ágat épít fel; az ``iteTru``, ``iteFal`` és ``iteSame``
   már meglévő feltételes tanúsítványt használ.
6. A ``weakening``, ``contradictionI`` és ``andI`` nem új primitív szabály:
   a nyolc konstruktorból megírt összetett program.

Ha egyetlen mondatot jegyzel meg, ez legyen az:

.. centered:: **a típus az úti cél, a program az útlevél, a Coq pedig a határőr.**
