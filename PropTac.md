# Coq taktikák a Prop típusra
A taktikák úgy viszonyulnak a levezetési szabályokhoz, hogy "visszafelé" töltik fel a bizonyításokat. A levezetésfék a gyökérpontból indulnak ki és a fában felfelé haladni a taktikákkal lehet. Amikor kész a bizonyítás, az elágazásakban a levezetési szabályok közvetítik az érvényességet. 
## És
### Bevezetési szabály:
````coq
Inductive and (A B : Prop) : Prop := conj : A -> B -> A /\ B.
````
$$ \dfrac{A:\text{Prop}\qquad B:\text{Prop}}
        {A\land B:\text{Prop}}\texttt{conj}$$

