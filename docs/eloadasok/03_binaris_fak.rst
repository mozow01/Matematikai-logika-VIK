3. előadás: Bináris fák és rekurzió
====================================

Az óra Coq-fájlja:
`3/treemaster.v <https://github.com/mozow01/Matematikai-logika-VIK/blob/main/3/treemaster.v>`_.

A bináris fa
-------------

Egy ``bintree`` vagy levél, vagy két bináris fából képzett csomópont.

.. code-block:: coq

   Inductive bintree : Type :=
   | leaf : bintree
   | node : bintree -> bintree -> bintree.

A konstruktorokból két bizonyítási eset adódik:

* ``leaf``: nincs részfa;
* ``node t1 t2``: két részfa van, ezért szerkezeti indukciónál két
  indukciós hipotézist kapunk.

Levélszám és magasság
---------------------

Mindkét függvény a fa szerkezetét követi.

.. code-block:: coq

   Fixpoint leaflength (t : bintree) : nat :=
     match t with
     | leaf => 1
     | node t1 t2 => leaflength t1 + leaflength t2
     end.

   Fixpoint height (t : bintree) : nat :=
     match t with
     | leaf => 0
     | node t1 t2 => 1 + Nat.max (height t1) (height t2)
     end.

Tehát egy levél levélszáma ``1``, magassága ``0``. Egy csomópont
levélszáma a két részfa levélszámának összege, magassága pedig a nagyobbik
részfa magasságánál eggyel nagyobb.

A ``⊕`` művelet
----------------

``t1 ⊕ t2`` a ``t1`` legjobboldalibb levelét a ``t2`` fával helyettesíti.

.. code-block:: coq

   Fixpoint oplus (t1 t2 : bintree) : bintree :=
     match t1 with
     | leaf => t2
     | node t11 t12 => node t11 (oplus t12 t2)
     end.

* Ha az első fa levél, akkor ezt kell lecserélni, ezért az eredmény ``t2``.
* Csomópontnál a bal részfa változatlan marad, a rekurzió csak a jobb
  részfában folytatódik.

1. gyakorló: konkrét kiértékelés
--------------------------------

Az alábbi három ``Compute`` eredményét válassza ki. A kód bemásolható a
``treemaster.v`` végére.

.. code-block:: coq

   Definition p :=
     node (node leaf leaf) (node leaf (node leaf leaf)).
   Definition q := node leaf leaf.

   Compute (p ⊕ q).
   Compute (leaflength (p ⊕ q)).
   Compute (height (p ⊕ q)).

.. raw:: html

   <div data-course-practice="tree-evaluation">
     <noscript>A gyakorló használatához engedélyezni kell a JavaScriptet.</noscript>
   </div>

Bizonyítás szerkezeti indukcióval
---------------------------------

Az ``oplus`` az első argumentumán rekurzív, ezért az ilyen tételeknél azon
érdemes indukciót végezni. A ``node`` esetben két indukciós hipotézis
keletkezik, de a definíció csak a jobb részfán hívja önmagát, ezért általában
``IHr`` használható.

2. gyakorló: bizonyítás kiegészítése
------------------------------------

Válassza ki a négy hiányzó Coq-parancsot. A teljes bizonyítás csak egy helyes
sorrendben áll össze.

.. code-block:: coq

   Theorem oplus_assoc :
     forall t1 t2 t3,
       (t1 ⊕ t2) ⊕ t3 = t1 ⊕ (t2 ⊕ t3).
   Proof.
     intros t1 t2 t3.
     induction t1 as [| l IHl r IHr].
     (* [1] *)
     (* [2] *)
       (* [3] *)
       (* [4] *)
   Qed.

.. raw:: html

   <div data-course-practice="tree-proof">
     <noscript>A gyakorló használatához engedélyezni kell a JavaScriptet.</noscript>
   </div>
