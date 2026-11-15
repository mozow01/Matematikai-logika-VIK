5. előadás: Implikáció és konjunkció
====================================

Az óra Coq-fájlja:
`5/implikacio_konjunkcio.v <https://github.com/mozow01/Matematikai-logika-VIK/blob/main/5/implikacio_konjunkcio.v>`_.
A részletesebb jegyzet a
`proofs_for_CS_students.pdf <https://github.com/mozow01/Matematikai-logika-VIK/blob/main/proofs_for_CS_students.pdf>`_
első két fejezete.

Bizonyítás mint program
-----------------------

A Coq-ban egy állítás típusként, a bizonyítása pedig ilyen típusú programként
olvasható.

* ``p : A`` azt jelenti, hogy ``p`` az ``A`` állítás bizonyítása.
* ``f : A -> B`` egy program, amely egy ``A`` bizonyításából ``B``
  bizonyítását készíti.
* ``p : A /\ B`` egy pár, amely egy ``A`` és egy ``B`` bizonyítást tartalmaz.

Implikáció
----------

Az implikációnak egy bevezetési és egy kiküszöbölési szabálya van.

.. math::

   \frac{\Gamma,,A \vdash B}{\Gamma \vdash A \to B}\;{\to I}
   \qquad
   \frac{\Gamma \vdash A \to B \qquad \Gamma \vdash A}
        {\Gamma \vdash B}\;{\to E}

Bevezetéskor ideiglenesen feltesszük ``A``-t. Ha ebből megkapjuk ``B``-t,
akkor a feltételt lezárva ``A -> B``-hez jutunk. Kiküszöböléskor egy
``A -> B`` programot alkalmazunk egy ``A`` bizonyítására.

Coqban:

* ``intro`` vagy ``intros`` vezeti be a feltételt;
* ``apply`` alkalmazza az implikációt;
* ``exact`` megadja a már rendelkezésre álló bizonyítást.

.. code-block:: coq

   Lemma implikacio_lanc : forall A B C : Prop,
     (A -> B) -> (B -> C) -> A -> C.
   Proof.
     intros A B C HAB HBC HA.
     apply HBC.
     apply HAB.
     exact HA.
   Qed.

A hozzá tartozó program:

.. code-block:: coq

   fun (A B C : Prop)
       (HAB : A -> B) (HBC : B -> C) (HA : A) =>
     HBC (HAB HA)

Ha egy bevezetett implikációt rögtön alkalmazunk, a köztes lépés elhagyható.
Programként ez a szokásos béta-redukció:

.. math::

   (\lambda x.\,p)(a) \longrightarrow_\beta p[a/x].

Konjunkció
----------

A konjunkció bevezetése párt készít. A két kiküszöbölési szabály a pár első,
illetve második tagját adja vissza.

.. math::

   \frac{\Gamma \vdash A \qquad \Gamma \vdash B}
        {\Gamma \vdash A \land B}\;{\land I}
   \qquad
   \frac{\Gamma \vdash A \land B}{\Gamma \vdash A}\;{\land E_1}
   \qquad
   \frac{\Gamma \vdash A \land B}{\Gamma \vdash B}\;{\land E_2}

Coqban:

* ``split`` két részcélra bontja az ``A /\ B`` célt;
* ``destruct H as [HA HB]`` szétszedi a ``H : A /\ B`` bizonyítást;
* programként ``conj HA HB`` épít párt, ``proj1 H`` és ``proj2 H`` pedig
  kiveszi a két tagját.

.. code-block:: coq

   Lemma konjunkcio_felcserel : forall A B : Prop,
     A /\ B -> B /\ A.
   Proof.
     intros A B H.
     destruct H as [HA HB].
     split.
     - exact HB.
     - exact HA.
   Qed.

Az implikáció és a konjunkció kapcsolata
----------------------------------------

Egy ``(A /\ B) -> C`` program egyszerre kapja meg ``A`` és ``B``
bizonyítását egy párban. Egy ``A -> B -> C`` program előbb ``A``-t, majd
``B``-t kapja meg. A két alak között mindkét irányban lehet fordítani:

.. code-block:: coq

   Theorem parbol_kulon : forall A B C : Prop,
     ((A /\ B) -> C) -> A -> B -> C.

   Theorem kulonbol_par : forall A B C : Prop,
     (A -> B -> C) -> (A /\ B) -> C.

Ezt a két átalakítást curryingnek és uncurryingnek nevezzük.

1. gyakorló: implikációs program
--------------------------------

Válassza ki azt a programot, amelynek pontosan az alábbi lemma a típusa.
Mindhárom lehetőség érvényes Coq-program, ezért a paraméterek sorrendjét is
ellenőrizni kell.

.. code-block:: coq

   Lemma implikacios_gyakorlo : forall A B C D : Prop,
     (A -> B) -> (B -> C) -> (C -> D) -> A -> D.

.. raw:: html

   <div data-lesson5-practice="implication-program">
     <noscript>A gyakorló használatához engedélyezni kell a JavaScriptet.</noscript>
   </div>

2. gyakorló: implikáció és konjunkció
-------------------------------------

Válassza ki azt a programot, amelynek pontosan az alábbi lemma a típusa.
Itt azt is figyelni kell, milyen sorrendben szerepel a pár két tagja.

.. code-block:: coq

   Lemma konjunkcios_gyakorlo : forall A B C : Prop,
     (A -> B) -> (A -> C) -> A -> B /\ C.

.. raw:: html

   <div data-lesson5-practice="conjunction-program">
     <noscript>A gyakorló használatához engedélyezni kell a JavaScriptet.</noscript>
   </div>
