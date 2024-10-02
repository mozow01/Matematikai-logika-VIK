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
#### Másik megoldás: enough

Ezt a két ágat az ````enough```` paranccsal is létre tudjuk hozni külön "kézzel", majd össze tudjuk kapcsolani conj-jal: 

````coq
Lemma andcomm_1' : forall A B : Prop, B /\ A -> A /\ B.
intros.
enough (H1 : A). 
enough (H2 : B). 
exact (conj H1 H2).
````
Itt az ````exact (conj H1 H2).```` sor hivatkozik a H1 és H2 levezetések konjunkciójára, de ehhez még később le kell gyártani az A és B egy-egy (H1, H2) bizonyítását.

exact előtt: 

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
