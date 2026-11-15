4. előadás: Indexelt fák és absztrakt szintaxisfák
==================================================

Az óra Coq-fájlja:
`4/TreeMaster2.v <https://github.com/mozow01/Matematikai-logika-VIK/blob/main/4/TreeMaster2.v>`_.

Magassággal indexelt fák
------------------------

A ``HTree n`` típusban az ``n`` index már a típusban rögzíti a fa
magasságát.

.. code-block:: coq

   Inductive HTree : nat -> Set :=
   | Hleaf : HTree 0
   | Hnode : forall n m,
       HTree n -> HTree m -> HTree (S (Nat.max n m)).

Ennek következményei:

* egy ``HTree n`` érték típusa tanúsítja a magasságát;
* a ``Height_lemma`` szerint a kiszámított magasság valóban ``n``;
* a két ág felcserélésekor ``Nat.max n m`` és ``Nat.max m n`` között kell
  átlépni a ``Nat.max_comm`` egyenlőséggel. Ezt a Coq transportként jeleníti
  meg.

Kifejezések és szintaxisfák
---------------------------

Az ``Exp`` közvetlenül logikai kifejezéseket ír le. Az ``AST`` külön tárolja
az egy- és kétargumentumú műveleteket.

.. code-block:: coq

   Inductive Exp : Set :=
   | AT : nat -> Exp
   | NOT : Exp -> Exp
   | AND : Exp -> Exp -> Exp
   | OR : Exp -> Exp -> Exp.

   Inductive AST : Set :=
   | leaf : nat -> AST
   | node1 : UnOp -> AST -> AST
   | node2 : BinOp -> AST -> AST -> AST.

Az atom sorszáma mindkét ábrázolásban ``nat``. A ``NOT`` egygyermekes, az
``AND`` és az ``OR`` kétgyermekes csomóponttá válik.

Fordítás és denotáció
---------------------

* ``Translater1 : Exp -> AST`` kifejezésből szintaxisfát készít.
* ``Translater2 : AST -> Exp`` a szintaxisfát kifejezéssé alakítja vissza.
* ``ExpDenote`` és ``ASTDenote`` egy ``v : nat -> bool`` értékelés mellett
  számítja ki a kétféle ábrázolás jelentését.

A ``Soundness2`` tétel azt mondja ki, hogy a fordítás nem változtatja meg a
jelentést:

.. code-block:: coq

   Theorem Soundness2 :
     forall e v,
       ExpDenote e v = ASTDenote (Translater1 e) v.

A bizonyítás az ``e`` szerkezete szerinti indukció. Az atom esete közvetlen,
az összetett esetekben a részkifejezések indukciós hipotéziseit használjuk.

1. gyakorló: fordítás és kiértékelés
------------------------------------

Válassza ki a három ``Compute`` eredményét. A kód a ``Soundness2`` tétel elé
másolható.

.. code-block:: coq

   Definition vPractice (n : nat) : bool :=
     match n with
     | 0 => false
     | 1 => true
     | _ => false
     end.

   Definition ePractice := OR (AT 0) (NOT (AT 1)).

   Compute (Translater1 ePractice).
   Compute (Translater2 (Translater1 ePractice)).
   Compute (ExpDenote ePractice vPractice).

.. raw:: html

   <div data-course-practice="ast-evaluation">
     <noscript>A gyakorló használatához engedélyezni kell a JavaScriptet.</noscript>
   </div>

Oda-vissza fordítás
-------------------

Az ``AST_roundtrip`` azt állítja, hogy egy szintaxisfa kifejezéssé, majd
vissza szintaxisfává fordítva nem változik meg. Az ``AST`` szerinti
indukcióban az ``UnOp`` és a ``BinOp`` értékét is fel kell bontani.

2. gyakorló: bizonyítás kiegészítése
------------------------------------

Válassza ki a négy hiányzó Coq-parancsot. A sorrend is a bizonyítás része.

.. code-block:: coq

   Theorem AST_roundtrip :
     forall t,
       Translater1 (Translater2 t) = t.
   Proof.
     intro t.
     induction t as [n | u t IH | b t1 IH1 t2 IH2].
     (* [1] *)
     (* [2] *)
     (* [3] *)
       (* [4] *)
   Qed.

.. raw:: html

   <div data-course-practice="ast-proof">
     <noscript>A gyakorló használatához engedélyezni kell a JavaScriptet.</noscript>
   </div>
