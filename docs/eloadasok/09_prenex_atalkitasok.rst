9. előadás: Prenex átalakítások
================================

Az óra Coq-fájlja:
`9/prenex_atalkitasok.v <https://github.com/mozow01/Matematikai-logika-VIK/blob/main/9/prenex_atalkitasok.v>`_.

Kiinduló helyzet
----------------

Legyen ``U : Type``, ``A : U -> Prop`` és ``B : Prop``. Az ``A x`` függ
``x``-től, ``B`` viszont nem. Ez felel meg annak a szokásos oldalfeltételnek,
hogy ``x`` nem szerepel szabadon ``B``-ben.

Az implikáció mellett négy alapvető kvantormozgatás van:

.. list-table::
   :header-rows: 1

   * - Kiinduló alak
     - Prenex alak
     - A teljes ekvivalenciához használt feltétel
   * - ``B -> forall x, A x``
     - ``forall x, B -> A x``
     - nincs további feltétel
   * - ``(exists x, A x) -> B``
     - ``forall x, A x -> B``
     - nincs további feltétel
   * - ``B -> exists x, A x``
     - ``exists x, B -> A x``
     - ``U`` nem üres és ``B \/ ~ B``
   * - ``(forall x, A x) -> B``
     - ``exists x, A x -> B``
     - ``U`` nem üres, továbbá ``(forall x, A x) \/ exists x, ~ A x``

Az első két sor feltétel nélkül konstruktív. Az utolsó két sor egyik iránya
szintén feltétel nélkül bizonyítható, a fordított irányhoz azonban tanút kell
választani. A táblázatban az ehhez használt, elegendő feltételek láthatók.

1. Univerzális kvantor az implikáció jobb oldalán
-------------------------------------------------

.. math::

   (B \to \forall x\,A(x))
   \quad\leftrightarrow\quad
   \forall x\,(B \to A(x)).

Balról jobbra rögzítünk egy tetszőleges ``x``-et és feltesszük ``B``-t. Az
eredeti függvény ``B`` bizonyításából előállítja ``forall x, A x``
bizonyítását, ezt alkalmazzuk a rögzített ``x``-re.

Jobbról balra feltesszük ``B``-t. Egy tetszőleges ``x`` esetén a kapott
``B -> A x`` függvényt alkalmazzuk erre a bizonyításra. Sem tanút, sem
esetfelbontást nem kell választani, ezért nincs további feltétel.

.. code-block:: coq

   Theorem prenex_forall_jobbra :
     forall (U : Type) (A : U -> Prop) (B : Prop),
       (B -> forall x, A x) <-> forall x, B -> A x.
   Proof.
     intros U A B.
     split.
     - intros H x HB.
       apply H.
       exact HB.
     - intros H HB x.
       apply H with (x := x).
       exact HB.
   Qed.

2. Egzisztenciális kvantor az implikáció bal oldalán
----------------------------------------------------

.. math::

   ((\exists x\,A(x)) \to B)
   \quad\leftrightarrow\quad
   \forall x\,(A(x) \to B).

Balról jobbra egy rögzített ``x`` és ``A x`` esetén az ``x`` tanúval
felépítjük az ``exists x, A x`` bizonyítást, majd használjuk az eredeti
implikációt.

Jobbról balra a kapott egzisztenciális feltevést bontjuk fel. A tanú legyen
``x``, bizonyítása pedig ``A x``. Az általános ``A x -> B`` állítást erre az
``x``-re alkalmazva megkapjuk ``B``-t. Itt sincs további feltétel.

.. code-block:: coq

   Theorem prenex_exists_balra :
     forall (U : Type) (A : U -> Prop) (B : Prop),
       ((exists x, A x) -> B) <-> forall x, A x -> B.
   Proof.
     intros U A B.
     split.
     - intros H x HAx.
       apply H.
       exists x.
       exact HAx.
     - intros H Hex.
       destruct Hex as [x HAx].
       apply H with (x := x).
       exact HAx.
   Qed.

3. Egzisztenciális kvantor az implikáció jobb oldalán
----------------------------------------------------------------
.. math::

   (B \to \exists x\,A(x))
   \quad\leftrightarrow\quad
   \exists x\,(B \to A(x)).

A jobbról balra irány feltétel nélkül konstruktív. Ha adott egy ``x`` és egy
``B -> A x`` bizonyítás, akkor ``B`` esetén ugyanazzal az ``x`` tanúval
felépíthető az egzisztenciális következmény.

A balról jobbra irányban viszont az eredmény akkor is kér egy konkrét ``x``
tanút, amikor ``B`` hamis. Az itt használt konstruktív bizonyításhoz ezért
két feltételt adunk meg:

* ``exists x : U, True``: ``U`` nem üres, tehát a hamis ``B`` ágában is van
  választható elem;
* ``B \/ ~ B``: el tudjuk dönteni, hogy az eredeti implikációból nyerünk-e
  ``A x`` tanút, vagy a hamis ``B`` miatt lesz igaz a ``B -> A x``.

A nemüresség valóban fontos: ha ``U`` üres és ``B`` hamis, a bal oldal igaz,
a jobb oldali egzisztenciális állítás viszont hamis.

.. code-block:: coq

   Theorem prenex_exists_jobbra :
     forall (U : Type) (A : U -> Prop) (B : Prop),
       (exists x : U, True) ->
       (B \/ ~ B) ->
       (B -> exists x, A x) <-> exists x, B -> A x.
   Proof.
     intros U A B NemUres DonthetoB.
     split.
     - intro H.
       destruct DonthetoB as [HB | HnB].
       + destruct (H HB) as [x HAx].
         exists x.
         intro HB2.
         exact HAx.
       + destruct NemUres as [x Igaz].
         exists x.
         intro HB.
         exfalso.
         apply HnB.
         exact HB.
     - intros H HB.
       destruct H as [x Hx].
       exists x.
       apply Hx.
       exact HB.
   Qed.

4. Univerzális kvantor az implikáció bal oldalán
------------------------------------------------

.. math::

   ((\forall x\,A(x)) \to B)
   \quad\leftrightarrow\quad
   \exists x\,(A(x) \to B).

A jobbról balra irány itt is feltétel nélkül konstruktív. A jobb oldal ad egy
``x``-et és egy ``A x -> B`` bizonyítást. A ``forall x, A x`` feltevésből
megkapjuk ``A x``-et, ebből pedig ``B``-t.

A balról jobbra irányban ismét konkrét tanút kell adnunk. Az itt használt
feltételek:

* ``exists x : U, True``: ha minden ``A x`` igaz, akkor is ki tudjunk
  választani egy elemet;
* ``(forall x, A x) \/ exists x, ~ A x``: vagy rendelkezésre áll a teljes
  univerzális bizonyítás, vagy kapunk egy konkrét ellenpéldát.

Az első ágban az eredeti implikáció megadja ``B``-t; ekkor bármelyik elem jó
tanú. A második ágban az ellenpélda legyen a tanú: ``A x`` feltevése
ellentmondásra vezet, abból pedig következik ``B``.

Fontos, hogy a ``forall x, A x \/ ~ A x`` pontonkénti eldönthetőség önmagában
nem feltétlenül adja a fenti teljes esetfelbontást egy tetszőleges végtelen
típuson. Véges ``U`` esetén viszont a pontonkénti döntésekből végig lehet
ellenőrizni az összes elemet.

.. code-block:: coq

   Theorem prenex_forall_balra :
     forall (U : Type) (A : U -> Prop) (B : Prop),
       (exists x : U, True) ->
       ((forall x, A x) \/ exists x, ~ A x) ->
       ((forall x, A x) -> B) <-> exists x, A x -> B.
   Proof.
     intros U A B NemUres DonthetoMinden.
     split.
     - intro H.
       destruct DonthetoMinden as [Hall | Hellenpelda].
       + destruct NemUres as [x Igaz].
         exists x.
         intro HAx.
         apply H.
         exact Hall.
       + destruct Hellenpelda as [x HnAx].
         exists x.
         intro HAx.
         exfalso.
         apply HnAx.
         exact HAx.
     - intros H Hall.
       destruct H as [x Hx].
       apply Hx.
       apply Hall.
   Qed.

Mit jelent itt a klasszikus változat?
-------------------------------------

Rögzített, nem üres alaphalmazon a klasszikus logika biztosítja a szükséges
esetfelbontásokat, ezért mind a négy sort egyszerű ekvivalenciaként szokás
használni. Coq-ban nem töltünk be klasszikus könyvtárat: a harmadik és
negyedik tétel állításában külön látszik, pontosan melyik döntést használja a
bizonyítás.

Rövid ellenőrzés
----------------

Mind a négy sorban válassza ki a kiinduló állítással ekvivalens prenex alakot
az adott feltételek mellett.

.. raw:: html

   <div class="practice-shell" data-lesson9-practice>
     <fieldset class="practice-card" data-answer="forall-right">
       <legend><code>B -&gt; forall x, A x</code></legend>
       <label class="practice-option"><input type="radio" name="lesson9-q1" value="forall-right"> <code>forall x, B -&gt; A x</code></label>
       <label class="practice-option"><input type="radio" name="lesson9-q1" value="exists-right"> <code>exists x, B -&gt; A x</code></label>
       <label class="practice-option"><input type="radio" name="lesson9-q1" value="forall-left"> <code>forall x, A x -&gt; B</code></label>
     </fieldset>
     <fieldset class="practice-card" data-answer="forall-left">
       <legend><code>(exists x, A x) -&gt; B</code></legend>
       <label class="practice-option"><input type="radio" name="lesson9-q2" value="exists-left"> <code>exists x, A x -&gt; B</code></label>
       <label class="practice-option"><input type="radio" name="lesson9-q2" value="forall-left"> <code>forall x, A x -&gt; B</code></label>
       <label class="practice-option"><input type="radio" name="lesson9-q2" value="forall-right"> <code>forall x, B -&gt; A x</code></label>
     </fieldset>
     <fieldset class="practice-card" data-answer="exists-right">
       <legend><code>B -&gt; exists x, A x</code>, ha <code>U</code> nem üres és <code>B \/ ~ B</code></legend>
       <label class="practice-option"><input type="radio" name="lesson9-q3" value="forall-right"> <code>forall x, B -&gt; A x</code></label>
       <label class="practice-option"><input type="radio" name="lesson9-q3" value="exists-right"> <code>exists x, B -&gt; A x</code></label>
       <label class="practice-option"><input type="radio" name="lesson9-q3" value="exists-left"> <code>exists x, A x -&gt; B</code></label>
     </fieldset>
     <fieldset class="practice-card" data-answer="exists-left">
       <legend><code>(forall x, A x) -&gt; B</code>, a fenti nemürességi és döntési feltételekkel</legend>
       <label class="practice-option"><input type="radio" name="lesson9-q4" value="forall-left"> <code>forall x, A x -&gt; B</code></label>
       <label class="practice-option"><input type="radio" name="lesson9-q4" value="exists-left"> <code>exists x, A x -&gt; B</code></label>
       <label class="practice-option"><input type="radio" name="lesson9-q4" value="exists-right"> <code>exists x, B -&gt; A x</code></label>
     </fieldset>
     <div class="practice-actions">
       <button class="practice-button" type="button" data-check>Ellenőrzés</button>
     </div>
     <p class="practice-feedback" data-feedback aria-live="polite"></p>
     <noscript>A gyakorló használatához engedélyezni kell a JavaScriptet.</noscript>
   </div>
