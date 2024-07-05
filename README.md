#  Alkalmazott matematikai logika

## Követelmény

## Hivatalos témák
Nagyon túlzsúfolt, ezért csak a vastagon szedettről lesz szó.

**Tárgynyelv-metanyelv, infix-prefix írásmód, nulladrendű-magasabbrendű nyelv, egyértelmű olvashatóság. A nyelv elemei. Formulák és kifejezések. Struktúra, algebra, modell. Interpretáció. Az „igazság" definíciója - a halmazelméletre építve. Igazsághalmazok és tulajdonságaik. Különféle típusú modellek: állítás, elsőrendű, modális, stb.** Példák mesterséges intelligenciabeli alkalmazásokra. **A logikai következmény fogalom. Dedukció tétel. Nevezetes logikai ekvivalenciák. Normálformák: konjunktív,** prenex, Skolem. **Az axiomatikus módszer. Levezetési és cáfolati bizonyítási rendszerek. Hilbert rendszer, analitikus fák, rezolúció. A logikai programozásról. Elmélet fogalma. Axiomatizálhatóság, eldönthetőség, ellentmondástalanság, teljesség. Kompaktsági tétel (szintaktikai). A gépi bizonyításról. A logika (matematika) szemantikai és bizonyításelméleti megközelítése egyenértékű: Gödel teljességi tétele és változatai. Bizonyításelméleti fogalmak modellelméleti jellemzései, modell módszer. Egy elmélet ellentmondástalan akkor és csak akkor ha kielégíthető. A kompaktsági tétel (szemantikai) és a végesítés fogalma. A bizonyításelmélet korlátai: Gödel inkomplettségi és Church eldönthetetlenségi tételei. E tételek interpretációi a tudomány metodológiában. A Löwenheim-Skolem típusú tételek és jelentőségük. Kitekintés a magasabb rendű logikákra. Néhány bonyolultsági osztály jellemzése logikai problémákkal, Fagin tétele.** A végtelen kicsiny mennyiség (infinitezimális) bevezetése egy modell konstrukció, az ultrahatvány ill. a kompaktsági tétel segítségével. A valós számfogalom bővítése: a hipervalós számok. Newton és Leibniz analízisének rekonstrukciója e fogalmak segítségével: Nem-standard analízis. A folytonosság, differenciálhatóság és integrálhatóság nem-standard definíciói. Néhány párhuzamba állítható logikai és Boole algebrai fogalom: elmélet - szűrő, komplettség - prím, levezethető - kisebb, axiómák üres halmaza - szabad algebra, axiómák feltételezése - relativizálás, stb. A szóban forgó kapcsolat alkalmazása a valószínűségszámításban (eseményalgebrák) és hálózatok elemzésénél. Általánosítások elsőrendű logikára.

## Miről szól a tárgy?

A logika a racionális érvelés egy formális modelljét adja. Sokféle logika van még a racionális érveléseken belül is, mi kettőt tanulunk:

* klasszikus logika (matematikusok logikája)
* konstruktivista (informatikusok és típuselmélészek logikája)

Lesz majd szó nullad, első és magasabbrendű logikáról. Ezek rendre a 

* kijelentéslogika,
* kvantifikáció elmélet és
* (adat)típuselmélet.

Lesz szó 

* szintaktikáról (nyelv vagy programnyelv),
* szemantikáról (amit jelent, intuitívan, halmazelméletileg, gráfelméletileg vagy algebrailag) és
* pragmatikáról (ahogy használjuk).

Van egy nagyon erős kapcsolat a programozás és az "informatikus" (konstruktív) logika között, ez a Curry--Howard-izomorfizmus. A klasszikus logikai tételek a halmazokhoz és a Boole-értékekhez kapcsolódnak.

Nagy segítségünkre lesz két teljes, tiszta, típusos, funkcionális programozási nyelv, a [Coq](https://coq.inria.fr/) és a [Lean4](https://leanprover.github.io/theorem_proving_in_lean4/), amelyek egyben egy bizonyítás asszisztensek, programnyelvek és programnyelv tervező szoftverek.  

Coq:

* 1989 Thierry **Coq**and, Inria France, 1989
* hézagmentes, teljes bizonyítás és verifikáció
* piacvezető informatikában
* C helyességbizonyító, 4 szín sejtés, Gödel-tétel bizonyítása.
* IDE is van hozzá (CoqIDE).

Lean4:
* **Leon**ardo de Moura, Microsoft Research, 2013
* matematikai könyvtára (Mathlib4) a teljes matematikus BSc anyagot tartalmazza
* Pilinomiális Freiman-Ruzsa sejtés, NF ellentmondásmentessége
* VSCode





