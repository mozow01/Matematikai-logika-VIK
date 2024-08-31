#  Matematikai logika
Alkalmazott lineáris algebra és matematikai logika

(Alkalmazott lineáris algebra) és matematikai logika

Alkalmazott (lineáris algebra és matematikai logika) -> (Alkalmazott lineáris algebra) és (Alkalmazott matematikai logika)

## Követelmény

### Kötelező tárgyként: 

* 10 beadandó Moodle feladat: 20 pont, nincs minimumkövetelmény, de beleszámít a pontszerzésbe.
* 1 zh (45 perc): 20 pont, minimumkövetelmény: 8 pont. 
* vizsga (45 perc): 10 pont, minimumkövetelmény: 4 pont.

A jegy a Lineráis algebra részből szerzett pontokból is összeáll.

### Szabadon válaszható tárgyként: 

* 10 beadandó Moodle feladat: 20 pont, minimumkövetelmény: 8 pont.

## Hivatalos témák
Túlzsúfolt, csak a vastagon szedet rész lesz.

**Tárgynyelv-metanyelv, infix-prefix írásmód, nulladrendű-magasabbrendű nyelv,** egyértelmű olvashatóság. **A nyelv elemei. Formulák és kifejezések. Struktúra, algebra, modell. Interpretáció. Az „igazság" definíciója - a halmazelméletre építve.** Igazsághalmazok és tulajdonságaik. **Különféle típusú modellek: állítás, elsőrendű,** modális, stb. **Példák mesterséges intelligenciabeli alkalmazásokra. A logikai következmény fogalom. Dedukció tétel. Nevezetes logikai ekvivalenciák. Normálformák:** konjunktív, **prenex,** Skolem. **Az axiomatikus módszer. Levezetési és cáfolati bizonyítási rendszerek. Hilbert rendszer, analitikus fák, rezolúció. A logikai programozásról. Elmélet fogalma. Axiomatizálhatóság, eldönthetőség, ellentmondástalanság, teljesség. Kompaktsági tétel (szintaktikai). A gépi bizonyításról. A logika (matematika) szemantikai és bizonyításelméleti megközelítése egyenértékű: Gödel teljességi tétele és változatai.** Bizonyításelméleti fogalmak modellelméleti jellemzései, modell módszer. Egy elmélet ellentmondástalan akkor és csak akkor ha kielégíthető. A kompaktsági tétel (szemantikai) és a végesítés fogalma. **A bizonyításelmélet korlátai: Gödel inkomplettségi és Church eldönthetetlenségi tételei. E tételek interpretációi a tudomány metodológiában.** A Löwenheim-Skolem típusú tételek és jelentőségük. **Kitekintés a magasabb rendű logikákra. Néhány bonyolultsági osztály jellemzése logikai problémákkal, Fagin tétele.** A végtelen kicsiny mennyiség (infinitezimális) bevezetése egy modell konstrukció, az ultrahatvány ill. a kompaktsági tétel segítségével. A valós számfogalom bővítése: a hipervalós számok. Newton és Leibniz analízisének rekonstrukciója e fogalmak segítségével: Nem-standard analízis. A folytonosság, differenciálhatóság és integrálhatóság nem-standard definíciói. Néhány párhuzamba állítható logikai és Boole algebrai fogalom: elmélet - szűrő, komplettség - prím, levezethető - kisebb, axiómák üres halmaza - szabad algebra, axiómák feltételezése - relativizálás, stb. A szóban forgó kapcsolat alkalmazása a valószínűségszámításban (eseményalgebrák) és hálózatok elemzésénél. Általánosítások elsőrendű logikára.

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

Van egy nagyon erős kapcsolat a programozás (funkcionális, típusos), a logika (konstruktív) és az algebra (kategóriaelmélet) között, ez a Curry--Howard-Lambek-izomorfizmus.

Nagy segítségünkre lesz két teljes, tiszta, típusos, funkcionális programozási nyelv, a [Coq](https://coq.inria.fr/) és a [Lean4](https://leanprover.github.io/theorem_proving_in_lean4/), amelyek egyben egy bizonyítás asszisztensek, programnyelvek és programnyelv tervező szoftverek.  

Coq:

* Thierry **Coq**and, Inria France, 1989-
* hézagmentes, teljes bizonyítás és verifikáció
* piacvezető informatikában
* C helyességbizonyító, 4 szín sejtés, Gödel-tétel bizonyítása.
* IDE is van hozzá (CoqIDE).

Lean4:
* **Leon**ardo de Moura, Microsoft Research, 2013-
* matematikai könyvtára (Mathlib4) a teljes matematikus BSc anyagot tartalmazza
* Polinomiális Freiman-Ruzsa sejtés (számtud), NF ellentmondásmentessége (logika)
* VSCode





