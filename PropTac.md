# Coq taktikák a Prop típusra
A taktikák úgy viszonyulnak a levezetési szabályokhoz, hogy "visszafelé" töltik fel a bizonyításokat. A levezetésfák a gyökérpontból indulnak ki és a fában felfelé haladni a taktikákkal lehet ("időutazás vissza az időben"). Amikor kész a bizonyítás, az elágazásokban a levezetési szabályok közvetítik az érvényességet. 
## És
### Bevezetési szabály:
````coq
Inductive and (A B : Prop) : Prop := conj : A -> B -> A /\ B.
````
$$ \dfrac{A:\text{Prop}\qquad B:\text{Prop}}
       {A\land B:\text{Prop}}\texttt{conj}$$

#### split

A ````split```` taktika a ````apply conj```` parancs rövidítése, amely a conj levezetési szabály alkalmazhatóságát kéri számond rajtunk: be tudjuk-e az és két igazságfeltételét bizonyítani. 

````coq
Lemma andcomm_1 : forall A B : Prop, B /\ A -> A /\ B.
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

