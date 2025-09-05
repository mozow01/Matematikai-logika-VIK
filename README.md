#  Matematikai logika
Alkalmazott lineáris algebra és matematikai logika

(Alkalmazott lineáris algebra) és matematikai logika

Alkalmazott (lineáris algebra és matematikai logika) -> (Alkalmazott lineáris algebra) és (Alkalmazott matematikai logika)

1. Bevezetés, ternáris kondicionális
2. Boole-típus, Boole-algebra
3. Szintaxisfák
4. Programfutás modellezése
5. Bizonyíthatóság (és, vagy, ha akkor)
6. Bizonyíthatóság (negáció)
7. Bizonyíthatóság (kvantorok)
8. Monadikus kvantorok, explicit helyettesítés
9. Prenex formulák
10. Kategorikus szemantika
11. Monádok
12. Kontinuáció
13. Fagin-tétel, automatikus bizonyításkeresés

## Követelmény

Matamatikai logika rész követelményei:

* 10 beadandó Moodle feladat: 20 pont, nincs minimumkövetelmény, de beleszámít a pontszerzésbe.
* 1 zh (45 perc): 20 pont, minimumkövetelmény: 8 pont. 
* vizsga (45 perc): 10 pont, minimumkövetelmény: 4 pont.

A tárgy teljes követelményrendszere: https://github.com/mozow01/Matematikai-logika-VIK/blob/main/2025_BMETE90MX75.pdf

A jegy a Lineráis algebra részből szerzett pontokból is összeáll.

## Miről szól a tárgy?

A logika a racionális érvelés egy formális modelljét adja. Sokféle logika van még a racionális érveléseken belül is, mi kettőt tanulunk:

* klasszikus logika (matematikusok logikája)
* konstruktivista (informatikusok logikája)

Lesz majd szó nullad, első és magasabbrendű logikáról. 

* kijelentéslogika,
* kvantifikáció elmélet és
* (adat)típuselmélet.

Lesz szó 

* szintaktikáról (nyelv vagy programnyelv),
* szemantikáról (amit jelent, operacionális, denotációs, algebrai) és
* pragmatikáról (ahogy használjuk, ahogy a programok futnak).

Van egy nagyon erős kapcsolat a programozás (funkcionális, típusos), a logika (konstruktív) és az algebra (kategóriaelmélet) között, ez a Curry--Howard--Lambek-izomorfizmus. Ez az absztraktsági szint a programnyelvek nagy részében elég, mert ha típusosak, akkor is polimorfak, ami elfér ebben a keretelméletben. A folytatás a függő típuselmélet (Martin-Löf típuselmélet), amely számunkra a natív nyelv, keretelmélet, metaelmélet.

Nagy segítségünkre lesz egy teljes, tiszta, típusos, funkcionális programozási nyelv, a [Coq](https://coq.inria.fr/) (vagy nagynéha a [Lean4](https://leanprover.github.io/theorem_proving_in_lean4/) ) ez egyben bizonyítás asszisztens, általános célú programnyelv és programnyelv tervező szoftver.  

Coq:

* Thierry **Coq**and, Inria France, 1989-
* hézagmentes, teljes bizonyítás és verifikáció
* piacvezető informatikában
* C helyességbizonyító, 4 szín sejtés, Gödel-tétel bizonyítása.
* IDE is van hozzá (CoqIDE).

(Lean4:

* **Leon**ardo de Moura, Microsoft Research, 2013-
* matematikai könyvtára (Mathlib4) a teljes matematikus BSc anyagot tartalmazza
* Polinomiális Freiman-Ruzsa sejtés (számtud), NF ellentmondásmentessége (logika)
* VSCode)





