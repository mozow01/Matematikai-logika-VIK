# Coq taktikák a Prop típusra
A taktikák úgy viszonyulnak a levezetési szabályokhoz, hogy "visszafelé" töltik fel a bizonyításokat. A levezetésfák a gyökérpontból indulnak ki és a fában felfelé haladni a taktikákkal lehet ("időutazás vissza az időben"). Amikor kész a bizonyítás, az elágazásokban a levezetési szabályok közvetítik az érvényességet. 

## Ha...akkor

A Coq funcionális programozási nyelv, ezért alapvető jelentősségű a függvénytípus, függvényképzés, függvény alkalmazás. A Coq-ban alapvető, belpített típus a függvénytípus, azért ennek a szabályai nem fedhetők fel úgy, ahogy a származtatott (definiált) induktív típusoknál. Ez kissé nehézséget jelent, mert se a Prop, se a Set, se a Type, se a ````forall T:A, U```` alakú termek esetén nem printelhetők ki ezek a szabályok. Minden olyan, amely az Inductive nevű induktív definícióval lett definiálva, igen (maga az Inductive definíció is induktív típus, az ő definíciója se érhető el). A dokumentációban persze benne vannak a megfelelő szabályok https://coq.inria.fr/doc/V8.20.0/refman/language/cic.html    

### Kiküszöbölési szabály
(Modus ponens)

$$\dfrac{f: A\to B\qquad a: A}{ f a: B}$$

A taktikák szintjén, az Ltac nyelvben ez a kövezkezőképpen mozgósítható:

````Coq
apply f.
````
vagy közvetlenül:
````Coq
exact (f a).
````

### Bevezetési szabály
(Dedukciótétel)

$$\dfrac{x: A\vdash y:B}{(\text{fun } (x : A) => (y:B)): A\to B}$$

Az ehhez kapcsolódó taktika a jól ismert 
````Coq
intros.
````

### Példák

````Coq
Lemma mp : forall A B : Prop, A -> (A -> B) -> B.
Proof.
intros.
apply H0.
assumption.
Qed.
`````

````Coq
Lemma mp' : forall A B : Prop, A -> (A -> B) -> B.
Proof.
intros A B a f.
exact (f a).
Qed.
````

````Coq
Lemma imp1 : forall A B : Prop, A -> A.
Proof.
intros.
exact H.
Show Proof.
Qed.
````

````Coq
imp1 = fun (A _ : Prop) (H : A) => H : forall A : Prop, Prop -> A -> A
````

````Coq
Lemma imp2 : forall A B : Prop, A -> (B -> A).
Proof.
intros.
exact H.
Show Proof.
Qed.
````

````Coq
Lemma imp2 : forall A B : Prop, A -> (B -> A).
Proof.
intros.
exact H.
Show Proof.
Qed.
````

````Coq
imp2 = fun (A B : Prop) (H : A) (_ : B) => H : forall A B : Prop, A -> B -> A
````

## És
### Bevezetési szabály
Ebben a pontban azt nézzük meg, hogy egy olyan állítást, amelyek a fő operátora az "és", hogyan igazolunk elsődlegesen. Erre való az "és" bevezetési szabálya (spéci esetben másképp is lehet, de mindig van olyan bizonyítás, amelyben ahhoz, hogy az "és" igaz, így érkezünk meg (Normálformatétel).)

````coq
Inductive and (A B : Prop) : Prop := conj : A -> B -> A /\ B.
````

$$ \dfrac{A:\text{Prop}\qquad B:\text{Prop}}
       {A\land B:\text{Prop}}\texttt{conj}$$

#### split

A ````split```` taktika a ````apply conj```` parancs rövidítése, amely a conj levezetési szabály alkalmazhatóságát kéri számond rajtunk: be tudjuk-e az és két igazságfeltételét bizonyítani. 

````coq
Lemma andcomm_1 : forall A B : Prop, B /\ A -> A /\ B.
Proof.
intros.
split.
````

A ````split```` taktika létrehozza azt a két ágat a levezetésfában, amely az ````A```` és a ````B```` címkékkel rendelkezik és az ````A/\B```` csúcsból ágazódik ketté a conj szabálynak megfelelően.

Előtte:

````coq
1 goal
A, B : Prop
H : B /\ A
______________________________________(1/1)
A /\ B
````

Utána: 

````coq
2 goals
A, B : Prop
H : B /\ A
______________________________________(1/2)
A
______________________________________(2/2)
B
````
#### Kézi megoldás: enough, assert

Ezt a két ágat az ````enough```` paranccsal is létre tudjuk hozni külön "kézzel", majd össze tudjuk kapcsolani conj-jal: 

````coq
Lemma andcomm_1' : forall A B : Prop, B /\ A -> A /\ B.
Proof.
intros.
enough (H1 : A). 
enough (H2 : B). 
exact (conj H1 H2).
````
Itt az ````exact (conj H1 H2).```` sor hivatkozik a H1 és H2 levezetések konjunkciójára, de ehhez még később le kell gyártani az A és B egy-egy (H1, H2) bizonyítását. Az exact taktikával kézzel (taktikázás nélkül) meg tudunk adni egy állításnak egy bizonyítását. A Gallina (Coq natív) egy funkcionális nyelv, ezért a ````conj```` két bemenetét kell megetetni a ````H1```` és ````H2```` termekkel. 

````exact```` előtt: 

````coq
3 goals
A, B : Prop
H : B /\ A
H1 : A
H2 : B
______________________________________(1/3)
A /\ B
______________________________________(2/3)
B
______________________________________(3/3)
A
````

Utána: 
````coq
2 goals
A, B : Prop
H : B /\ A
H1 : A
______________________________________(1/2)
B
______________________________________(2/2)
A
````
Az ````assert````-tel nem ússzuk meg azt, hogy a konjunkció tényezőit igazoló levezetéseket tényéleg el kell készítenünk maradéktalanul és utána fűzhetjük össze conj-jal. Lent az ````intuition```` taktika egy kicsit csalás, mert ez egy automatikus bizonyító modul, ami éppen ezt a picit levezetést magától is megcsinálja, de a követkető pontban meglesznek ezek is. 

````coq
Lemma andcomm_1'' : forall A B : Prop, B /\ A -> A /\ B.
Proof.
intros.
assert (H1 : A).
intuition. 
assert (H2 : B).
intuition. 
exact (conj H1 H2).
Qed.
````
### Kiküszöbölési szabály
Az indukciós vagy eliminációs szabály egy jellegzetes esetet mutatva arra enged következtetni, hogy ha egy konjunkcióról tudjuk, hogy igaz, akkor belőle egy harmadik állítást mikor tudunk levezetni.

````coq
and_ind : forall A B P : Prop, (A -> B -> P) -> A /\ B -> P
````

$$\dfrac{\begin{matrix}
\quad
\\
\quad
\\
A\land B
\end{matrix} \quad \begin{matrix}[A,B]\\
\vdots\\
P \end{matrix}}{P}\texttt{andind}$$

Az ````apply and_ind with (P:="...") in H```` parancs szolgál az indukciós szabály általános használatára. 

Az indukciós szabálynál van egy konkrétabb, amelyet inkább használunk, a destruktor. Az "és" konnektívumnak van két jellegzetes **destruktora,** amelyek az első és a második tényezőjét olvassák ki egy "és" típusú adatból:

$$\dfrac{
A\land B
}{A}\quad\dfrac{
A\land B
}{B}$$

Ez a Prop típusra nincs megírva, bár seperc alatt levezethető:

````coq
fstP := fun (A B : Prop) (H : A /\ B) =>
              match H with
              | conj x _ => x
              end
     : forall A B : Prop, A /\ B -> A

sndP := fun (A B : Prop) (H : A /\ B) =>
              match H with
              | conj _ y => y
              end
     : forall A B : Prop, A /\ B -> B
````

Nem kell azonban ezeket se használni, mert a destruktorok által visszaadott termek mind legyártódnak és feltételként építődnek be a ````destruct H as [H1 H2]```` taktikával:

````coq
Lemma andcomm_2 : forall A B : Prop, A /\ B -> B /\ A.
Proof.
intros.
destruct H as [H1 H2].
````

````destruct```` előtt: 

````coq
1 goal
A, B : Prop
H : A /\ B
______________________________________(1/1)
B /\ A
````

és után: 

````coq
1 goal
A, B : Prop
H1 : A
H2 : B
______________________________________(1/1)
B /\ A
````

Mivel az "és" az egyik legegyszerűbb típus, ezért a fenti taktikát még az ````elim H````/````induction H```` (jelentése: az indukciós szabály alkalmazása úgy, hogy a P közvetlenül a Goal lesz) és az ````inversion H```` (jelentése: mit tehetünk fel, ha a konnektívum, jelen esetben az "és" igaz) is helyettesíti, de csak azért mert ebben az esetben ők egybeesnek. Más típusoknál az ````elim H````/````induction H```` és az ````inversion H```` nagyon nem esnek egybe...

HF: az "és" asszociatív szabályának igazolása.
