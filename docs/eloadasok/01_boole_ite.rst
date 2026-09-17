1. óra: Boole-kifejezések és a ternáris kondicionális
=====================================================

Írni fogunk egy programnyelvet, ami a logikát progrmaozza le. Két szint lesz: programok (milyen tanúsítványai lesznek az igaz állításoknak) és a programok típusai (ezek lesznek az állítások). Ezen az órán a típusok nyelvét építjünk fel.

Az óra alapfájlja az
`1/ite.v <https://github.com/mozow01/Matematikai-logika-VIK/blob/main/1/ite.v>`_.
Töltsd le, nyisd meg CoqIDE-ban vagy VS Code-ban, és a saját próbáidat a fájl
aljára írd. A lapon található zöld interaktív ablakok ugyanezeket a fogalmakat
telepítés nélkül is kipróbálhatóvá teszik.

Három nézőpont ugyanarra a kifejezésre
--------------------------------------

.. raw:: html

   <div class="concept-grid">
     <section class="concept-card">
       <h3>Szintaxis</h3>
       <p>Milyen konstruktorokból és milyen sorrendben épül fel a fa?</p>
       <p><code>Boole</code></p>
     </section>
     <section class="concept-card">
       <h3>Denotáció</h3>
       <p>Melyik igazságértéket jelenti a teljes kifejezés?</p>
       <p><code>denote : Boole → bool</code></p>
     </section>
     <section class="concept-card">
       <h3>Kiértékelés</h3>
       <p>Milyen lépésekkel jutunk el egy egyszerű eredményig?</p>
       <p><code>beta_reduce : Boole → Boole</code></p>
     </section>
   </div>

Ugyanazt a bemenetet két különböző függvénynek is át fogjuk adni, az egyik egy fordító progam a Coq beépített bool típusába (denotáció szemantika), a másik a programfutást modellezi (operacionális szemantika).

.. math::

   A:\mathsf{Boole}
   \qquad
   \begin{cases}
   \mathsf{denote}(A):\mathsf{bool},\\
   \mathsf{beta\_reduce}(A):\mathsf{Boole}.
   \end{cases}

A két kimeneti típus különbözik. Ez később nagyon fontos lesz: ``Tru`` és
``true`` nem ugyanaz a Coq-érték, az első a "játéknyelvi" érték, a másik a Coq belső bool értéke.

A ``Boole`` nyelv szintaxisa
----------------------------

Ez a "játéknyelv" az igaz-hamist és a ternáris kondicionálist adja meg. A nyelvtant a számítógéptudományban szokásos módon Bachus--Naur-formában adjuk meg:

.. math::

   A ::= \mathsf{Tru}
       \mid \mathsf{Fal}
       \mid \mathsf{Ite}\;A\;A\;A.

Ez egy rekurzív definíció: az ``Ite`` ("if-then-else") mindhárom helyére ismét tetszőleges
``Boole``-kifejezés kerülhet. A Coq-definíció ennek szinte szó szerinti
fordítása:

.. code-block:: coq

   Inductive Boole : Type :=
   | Tru : Boole
   | Fal : Boole
   | Ite : Boole -> Boole -> Boole -> Boole.

Az ``Inductive`` primitív rekurzív, azaz építgetős módon egy új típust vezet be. A három sor a típus úgy nevezett **konstruktorait**, azaz építési szabályait
adja meg.

.. list-table:: Konstruktorok
   :header-rows: 1
   :widths: 18 32 50

   * - Konstruktor
     - Típus
     - Szerep
   * - ``Tru``
     - ``Boole``
     - igaz konstans, a szintaxisfa egy levele
   * - ``Fal``
     - ``Boole``
     - hamis konstans, a szintaxisfa egy levele
   * - ``Ite``
     - ``Boole -> Boole -> Boole -> Boole``
     - feltétel, akkor-ág és különben-ág összekapcsolása

Az ``Ite A B C`` olvasata:

    ha ``A``, akkor ``B``, különben ``C``.

Az argumentumok sorrendje tehát nem felcserélhető. Az első a feltétel, a
második az akkor-ág, a harmadik a különben-ág.

Példa szintaxisfára
~~~~~~~~~~~~~~~~~~~

Tekintsük ezt a kifejezést:

.. code-block:: coq

   Ite (Ite Fal Tru Fal) Tru Fal

A gyökér a külső ``Ite``, amelynek három részfája van:

.. code-block:: text

   Ite
   ├── Ite
   │   ├── Fal
   │   ├── Tru
   │   └── Fal
   ├── Tru
   └── Fal

Ez nem egy kételemű típus. Bár csak két konstansunk van, az ``Ite``
segítségével tetszőlegesen nagy szintaxisfákat készíthetünk. A Coq beépített,
valóban kételemű típusa majd a kisbetűs ``bool`` lesz.

Helyes és hibás kifejezések
~~~~~~~~~~~~~~~~~~~~~~~~~~~

.. code-block:: coq

   Tru                         (* helyes: Boole *)
   Ite Tru Fal Tru             (* helyes: Boole *)
   Ite (Ite Fal Tru Fal) Tru Fal

   Ite Tru Fal                 (* hibás: hiányzik a harmadik argumentum *)
   Ite true Fal Tru            (* hibás: true : bool, nem Boole *)

A ``Check`` nem futtatja a kifejezést, hanem megkérdezi a Coq-tól a típusát:

.. code-block:: coq

   Check Tru.
   Check Ite.
   Check (Ite Tru Fal Tru).

Próbáld átírni az alábbi ablakban a ``syntax_pelda`` definícióját, majd
léptesd végig a parancsokat.

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=syntax"
     title="A Boole-kifejezések szintaxisának interaktív Coq-példája"
     loading="lazy" allow="clipboard-write"></iframe>

Származtatott műveletek
-----------------------

A ``Boole`` típusnak továbbra is csak három konstruktora van. Mégis kényelmes
neveket adhatunk gyakran használt logikai operátoroknak, mert a ternáris kondicionális tökéletesen alkalmas arra, hogy az összes logikai operátor kifejezhető legyen vele. Ezek **definíciók**, így tehát már nem
új konstruktorok.

Negáció
~~~~~~~

Ha ``A`` igaz, a negáció legyen hamis; ha ``A`` hamis, legyen igaz:

.. code-block:: coq

   Definition Neg (A : Boole) : Boole :=
     Ite A Fal Tru.

Az ``unfold Neg`` a ``Neg`` nevet lecseréli a definíció jobb oldalára:

.. code-block:: coq

   Example neg_kibontasa :
     Neg Fal = Ite Fal Fal Tru.
   Proof.
     unfold Neg.
     reflexivity.
   Qed.

Itt még nem kellett kiértékelni a feltételt. Csak megmutattuk, hogy a bal és
a jobb oldal a definíció kibontása után ugyanaz a kifejezés.

Konjunkció kétféleképpen
~~~~~~~~~~~~~~~~~~~~~~~~

A konjunkció teljesen kifejtett változata:

.. code-block:: coq

   Definition And (A B : Boole) : Boole :=
     Ite A (Ite B Tru Fal) Fal.

Ennek olvasata:

* ha ``A`` hamis, az eredmény rögtön ``Fal``;
* ha ``A`` igaz, megvizsgáljuk ``B``-t;
* ``B`` igaz értékénél ``Tru``, hamis értékénél ``Fal`` az eredmény.

Ugyanezt rövidebben is leírhatjuk:

.. code-block:: coq

   Definition And2 (A B : Boole) : Boole :=
     Ite A B Fal.

Ha ``A`` igaz, egyszerűen ``B`` lesz az eredmény; ha ``A`` hamis, ``Fal``.
Ez ugyanazt az igazságfüggvényt írja le, de nem ugyanazt a szintaxisfát.

.. list-table:: A konjunkció elvárt értékei
   :header-rows: 1
   :align: center

   * - ``A``
     - ``B``
     - ``A`` és ``B``
   * - ``Fal``
     - ``Fal``
     - ``Fal``
   * - ``Fal``
     - ``Tru``
     - ``Fal``
   * - ``Tru``
     - ``Fal``
     - ``Fal``
   * - ``Tru``
     - ``Tru``
     - ``Tru``

.. note:: Definíció és futás

   Az ``unfold`` egy név definícióját bontja ki. A ``beta_reduce`` később a
   kapott ``Ite``-fát értékeli ki. Ez két külön művelet.

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=operations"
     title="A származtatott Boole-műveletek interaktív Coq-példája"
     loading="lazy" allow="clipboard-write"></iframe>

Denotációs szemantika
---------------------

A szintaxisfa önmagában csak szerkezet. Jelentést pl. úgy adunk neki, hogy minden
``Boole``-kifejezéshez hozzárendelünk egy Coq-értéket. Ilyen szempontból most két szintünk van. Van a tárgynyelv (az Ite) és a metanyelv, a natív Coq. A denotációs szemantika nagyon kis igényű: lényegében egy szótár vagy még annál is kevesebb. Ha komoly "jelentéselméletet" akarunk csinálni, ami valóban magyaráz, akkor a nyelv gyakorlati használtát is be kell mutatnun. Ez lesz majd később az operacionális szemantika.

.. math::

   [[\_]] : \mathsf{Boole}\longrightarrow\mathsf{bool}.

A fájlban ezt a függvényt ``denote``-nak hívjuk:

.. code-block:: coq

   Fixpoint denote (A : Boole) : bool :=
     match A with
     | Tru => true
     | Fal => false
     | Ite A B C =>
         if denote A then denote B else denote C
     end.

A két szintet következetesen külön jelöljük:

.. list-table:: Saját nyelv és Coq-érték
   :header-rows: 1
   :widths: 30 35 35

   * - Szint
     - Igaz
     - Hamis
   * - saját szintaxis: ``Boole``
     - ``Tru``
     - ``Fal``
   * - Coq beépített típusa: ``bool``
     - ``true``
     - ``false``

Az ``Ite`` denotációjánál először a feltétel jelentését számítjuk ki. Ha ez
``true``, a második; ha ``false``, a harmadik argumentum jelentését vesszük.

Kézi számítás
~~~~~~~~~~~~~

Legyen

.. code-block:: coq

   A := Ite (Ite Fal Fal Tru) Tru Fal.

A belső feltétel denotációja ``false``, ezért a belső ``Ite`` a harmadik
ágának denotációját, vagyis ``true``-t adja. A külső feltétel így ``true``,
tehát a külső ``Ite`` második ága következik:

.. math::

   \begin{aligned}
   \mathsf{denote}(\mathsf{Ite}\;\mathsf{Fal}\;\mathsf{Fal}\;\mathsf{Tru})
      &= \mathsf{true},\\
   \mathsf{denote}(A)
      &= \mathsf{denote}(\mathsf{Tru})
       = \mathsf{true}.
   \end{aligned}

A Coq ugyanezt a ``Compute`` paranccsal kiszámítja:

.. code-block:: coq

   Compute denote (Ite (Ite Fal Fal Tru) Tru Fal).
   (* = true : bool *)

Denotációs azonosság
~~~~~~~~~~~~~~~~~~~~

Az ``And`` és az ``And2`` különböző kifejezésfát készít, de minden bemeneten
ugyanaz a jelentésük. Ezt egy tétel mondja ki:

.. code-block:: coq

   Theorem And_denote_2 :
     forall A B,
       denote (And2 A B) = denote (And A B).

A bizonyításban az ``intros`` rögzíti a két tetszőleges bemenetet, az
``unfold`` kibontja a definíciókat, a ``destruct`` pedig végignézi a
lehetséges igazságértékeket:

.. code-block:: coq

   Proof.
     intros A B.
     unfold And2, And.
     simpl.
     destruct (denote A), (denote B); reflexivity.
   Qed.

Tehát, eltérő programok ugyanazt a
fordítási értéket adják. A taktikákat az interaktív ablakban lépésenként
is meg lehet figyelni.

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=denotation"
     title="A denotációs szemantika interaktív Coq-példája"
     loading="lazy" allow="clipboard-write"></iframe>

Operacionális szemantika: ``beta_reduce``
-----------------------------------------

A denotáció közvetlenül egy ``bool`` értéket ad. Az operacionális szemantika
ezzel szemben azt írja le, hogyan értékeljük ki a saját nyelvünk
kifejezéseit, hogyan futnak le a típusnyelv programjai. Az eredmény ``Boole`` típusú lesz, mert azt szeretnénk megérteni, mit lehet csinálni ezekkel a kifejezésekkel, hogyan futnak le a programok. A programfutást modellező függvény a **beta-redukció.**

.. code-block:: coq

   Fixpoint beta_reduce (A : Boole) : Boole :=
     match A with
     | Tru => Tru
     | Fal => Fal
     | Ite A B C =>
         match beta_reduce A with
         | Tru => beta_reduce B
         | Fal => beta_reduce C
         | A' => Ite A' B C
         end
     end.

A működés sorrendje:

1. ``Tru`` és ``Fal`` már eredmény, ezért változatlan marad.
2. ``Ite A B C`` esetén először csak ``A``-t értékeljük ki.
3. Ha ``A`` eredménye ``Tru``, ``B``-vel folytatjuk.
4. Ha ``A`` eredménye ``Fal``, ``C``-vel folytatjuk.
5. A nem választott ágat nem kell kiértékelni.

A belső ``match`` harmadik, ``A'`` ága azért szerepel a definícióban, mert a
Coq-ban minden konstruktort le kell fednünk. Ez az ág egy még nem eldöntött
feltételes kifejezést változatlanul a helyén hagyna. A fájl végén szereplő
normalizációs tétel igazolja, hogy zárt ``Boole``-kifejezés teljes rekurzív
kiértékelése valójában mindig ``Tru`` vagy ``Fal`` lesz.

Lépésenkénti példa
~~~~~~~~~~~~~~~~~~

.. code-block:: coq

   beta_reduce (Ite (Ite Fal Fal Tru) Tru Fal)

Először a külső feltételt redukáljuk:

.. code-block:: text

   beta_reduce (Ite Fal Fal Tru)
   = beta_reduce Tru
   = Tru

Ezért a külső ``Ite`` akkor-ágát választjuk:

.. code-block:: text

   beta_reduce (Ite (Ite Fal Fal Tru) Tru Fal)
   = beta_reduce Tru
   = Tru

A Coq-ban a zárt számítások gyakran már ``reflexivity``-vel igazolhatók,
mert a definíciók kiszámolódnak:

.. code-block:: coq

   Example beta_pelda :
     beta_reduce (Ite Fal (Ite Fal Fal Tru) Tru) = Tru.
   Proof.
     simpl.
     reflexivity.
   Qed.

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=reduction"
     title="A beta_reduce interaktív Coq-példája"
     loading="lazy" allow="clipboard-write"></iframe>

Mit jelent az, hogy „ugyanaz”?
--------------------------------

Ez az óra legfontosabb megkülönböztetése. Két kifejezés többféle értelemben
is összehasonlítható.

Szintaktikus azonosság
~~~~~~~~~~~~~~~~~~~~~~

Ugyanazokból a konstruktorokból, ugyanabban a faalakban épülnek fel. Például

.. code-block:: coq

   Ite Tru Fal Tru

nem ugyanaz a szintaxisfa, mint

.. code-block:: coq

   Fal

Az első gyökere ``Ite`` és három gyereke van, a második egyetlen levél.

Azonos kiértékelési eredmény
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A két különböző fa ugyanarra a ``Boole``-értékre redukálódhat:

.. code-block:: coq

   beta_reduce (Ite Tru Fal Tru) = Fal
   beta_reduce Fal                = Fal

Azonos denotáció
~~~~~~~~~~~~~~~~

A két kifejezés ugyanazt a beépített igazságértéket jelentheti:

.. code-block:: coq

   denote (Ite Tru Fal Tru) = false
   denote Fal                = false

Az összehasonlítás összefoglalása:

.. list-table:: Három különböző kérdés
   :header-rows: 1
   :widths: 27 25 24 24

   * - Kifejezéspár
     - Ugyanaz a szintaxisfa?
     - Azonos redukált eredmény?
     - Azonos denotáció?
   * - ``Ite Tru Fal Tru`` és ``Fal``
     - nem
     - igen: ``Fal``
     - igen: ``false``
   * - ``And Tru Tru`` és ``And2 Tru Tru``
     - nem
     - igen: ``Tru``
     - igen: ``true``
   * - ``Ite Fal Tru Fal`` és ``Tru``
     - nem
     - nem
     - nem
   * - ``Tru`` és ``Tru``
     - igen
     - igen
     - igen

.. warning:: Pontos fogalmazás

   A „két kifejezés egyenlő” mondat önmagában félreérthető. Mindig mondd meg,
   hogy azonos szintaxisfáról, azonos redukált eredményről vagy azonos
   denotációról beszélsz. A programegyenlőség a számítógéptudomány centrális fogalma.

Az alábbi Coq-példa ugyanarra a párra három külön állítást fogalmaz meg.

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=comparison"
     title="A szintaxis, a redukció és a denotáció összehasonlításának interaktív Coq-példája"
     loading="lazy" allow="clipboard-write"></iframe>

Matematikai tételek
------------------------------------

A matematikusok szeretnel tételeket kimondani vizsgálódásuk tárgyairól, itt most két tétel lesz.

Normálforma
~~~~~~~~~~~

Egy kifejezés akkor van normálformában, ha ``Tru`` vagy
``Fal``:

.. code-block:: coq

   Definition is_normal (A : Boole) : Prop :=
     A = Tru \/ A = Fal.

A ``weak_normalization`` tétel azt mondja ki, hogy minden ``Boole``-kifejezés
teljes beta-redukció általi kiértékelése normálforma:

.. code-block:: coq

   Theorem weak_normalization :
     forall A : Boole,
       is_normal (beta_reduce A).

A bizonyítás ``A`` felépítése szerinti indukció. A ``Tru`` és ``Fal`` eset
közvetlen. Az ``Ite A1 A2 A3`` esetben az ``A1``-hez kapott indukciós
feltevés mondja meg, hogy a feltétel ``Tru`` vagy ``Fal`` lesz. Ezután rendre
az ``A2`` vagy az ``A3`` részfára vonatkozó indukciós feltevés zárja le a
bizonyítást.

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=normalization"
     title="A gyenge normalizáció tételének interaktív Coq-bizonyítása"
     loading="lazy" allow="clipboard-write"></iframe>

A redukció megőrzi a jelentést
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

A ``denote_beta`` tétel szerint a kiértékelés (beta-redukció) nem változtatja meg a kifejezés
fordítás utáni értékét:

.. code-block:: coq

   Theorem denote_beta :
     forall A : Boole,
       denote (beta_reduce A) = denote A.

Ezt egy felcserélhető diagrammal szemléltethetjük:

.. math::

   \begin{array}{ccc}
   A & \xrightarrow{\ \mathsf{beta\_reduce}\ } & \mathsf{beta\_reduce}(A)\\
   {\scriptstyle\mathsf{denote}}\downarrow && \downarrow{\scriptstyle\mathsf{denote}}\\
   \mathsf{bool} & \xrightarrow{\qquad\mathsf{id}\qquad} & \mathsf{bool}
   \end{array}

Akár előbb értékelünk ki és utána vesszük a jelentést, akár közvetlenül
vesszük a jelentést, ugyanahhoz a ``bool`` értékhez jutunk.

A bizonyítás itt is a kifejezés felépítése szerinti indukció. Az ``Ite``
esetben háromfelé bontjuk azt, hogy mire redukálódik a feltétel. A
feltételhez tartozó indukciós feltevés kapcsolja össze a redukált feltétel és
az eredeti feltétel denotációját; ezután a kiválasztott ág indukciós
feltevését használjuk.

.. raw:: html

   <iframe class="rocq-frame rocq-frame--example"
     src="../_static/rocq/ite-playground.html?example=denote_beta"
     title="A denote_beta tétel interaktív Coq-bizonyítása"
     loading="lazy" allow="clipboard-write"></iframe>

Gyakorlófeladatok
-----------------

Az első feladat egy összetett kifejezés teljes kiértékelési láncát kéri. A
másodikban egy igazságtáblához kell kiválasztani a megfelelő Coq-definíciót.
Mindkét helyen négy változat közül választ az oldal, ezért összesen tizenhat
különböző párosítás gyakorolható.

.. raw:: html

   <div class="practice-shell" data-boole-practice>
     <noscript>A gyakorlófeladatokhoz engedélyezni kell a JavaScriptet.</noscript>
   </div>

Óra végi ellenőrzőlista
-----------------------

Mielőtt továbblépsz, próbáld meg segítség nélkül megválaszolni ezeket:

1. Miért van végtelen sok ``Boole``-kifejezés, ha csak három konstruktor van?
2. Mi a különbség ``Tru`` és ``true`` között?
3. Mi az ``Ite A B C`` három argumentumának szerepe?
4. Az ``And`` új konstruktor vagy definiált rövidítés?
5. Milyen típusú a ``denote A`` eredménye?
6. Milyen típusú a ``beta_reduce A`` eredménye?
7. Lehet-e két különböző szintaxisfának azonos denotációja?
8. Miért csak az egyik ágat folytatjuk egy ``Ite`` kiértékelésekor?
