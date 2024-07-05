#  Alkalmazott matematikai logika

## Hivatalos témák
Nagyon túlzsúfolt, ezért csak a vastagon szedettről lesz szó.

**Tárgynyelv-metanyelv, infix-prefix írásmód, nulladrendű-magasabbrendű nyelv, egyértelmű olvashatóság. A nyelv elemei. Formulák és kifejezések. Struktúra, algebra, modell. Interpretáció. Az „igazság" definíciója - a halmazelméletre építve. Igazsághalmazok és tulajdonságaik. Különféle típusú modellek: állítás, elsőrendű, modális, stb.** Példák mesterséges intelligenciabeli alkalmazásokra. **A logikai következmény fogalom. Dedukció tétel. Nevezetes logikai ekvivalenciák. Normálformák: konjunktív,** prenex, Skolem. **Az axiomatikus módszer. Levezetési és cáfolati bizonyítási rendszerek. Hilbert rendszer, analitikus fák, rezolúció. A logikai programozásról. Elmélet fogalma. Axiomatizálhatóság, eldönthetőség, ellentmondástalanság, teljesség. Kompaktsági tétel (szintaktikai). A gépi bizonyításról. A logika (matematika) szemantikai és bizonyításelméleti megközelítése egyenértékű: Gödel teljességi tétele és változatai. Bizonyításelméleti fogalmak modellelméleti jellemzései, modell módszer. Egy elmélet ellentmondástalan akkor és csak akkor ha kielégíthető. A kompaktsági tétel (szemantikai) és a végesítés fogalma. A bizonyításelmélet korlátai: Gödel inkomplettségi és Church eldönthetetlenségi tételei. E tételek interpretációi a tudomány metodológiában. A Löwenheim-Skolem típusú tételek és jelentőségük. Kitekintés a magasabb rendű logikákra. Néhány bonyolultsági osztály jellemzése logikai problémákkal, Fagin tétele.** A végtelen kicsiny mennyiség (infinitezimális) bevezetése egy modell konstrukció, az ultrahatvány ill. a kompaktsági tétel segítségével. A valós számfogalom bővítése: a hipervalós számok. Newton és Leibniz analízisének rekonstrukciója e fogalmak segítségével: Nem-standard analízis. A folytonosság, differenciálhatóság és integrálhatóság nem-standard definíciói. Néhány párhuzamba állítható logikai és Boole algebrai fogalom: elmélet - szűrő, komplettség - prím, levezethető - kisebb, axiómák üres halmaza - szabad algebra, axiómák feltételezése - relativizálás, stb. A szóban forgó kapcsolat alkalmazása a valószínűségszámításban (eseményalgebrák) és hálózatok elemzésénél. Általánosítások elsőrendű logikára.

## Miről szól a tárgy?

A logika a racionális érvelés egyes formális modelljét adja. Sokféle logika van még a racionális érveléseken belül is, mi kettőt tanulunk:

* klasszikus logika (matematikusok)
* konstruktivista (informatikusok) 

Lesz majd szó nullad, első és magasabbrendű logikáról. Ezek rendre a 

* kijelentéslogika,
* kvantifikáció elmélet és
* (adat)típuselmélet.

Lesz szó 

* szintaktikáról (nyelv vagy programnyelv),
* szemantikáról (amit jelent, intuitívan, halmazelméletileg, gráfelméletileg vagy algebrailag) és
* pragmatikáról (ahogy használjuk).

Van egy nagyon erős kapcsolat a programozás és az informatikus logika között, ez a Curry--Howard-izomorfizmus. De a klasszikus logikai tételek is fontosak, amit meg inkább a halmazokhoz és Boole-értékekhez kapcsolódik.

Nagy segítségünkre lesz a teljes, tiszta, típusos, funkcionális programozási nyelv, a [Coq](https://coq.inria.fr/), amely egyben egy proof assistant is és egyben egy programnyelv tervező szoftver is. IDE is van hozzá (CoqIDE). Mit kell tudni a Coq-ról?

* 1989 Thierry Coqand, Inria France, 1989
* hézagmentes bizonyítás
* abszolút bizonyítás
* piacvezető
* C helyességbizonyító, 4 szín sejtés, Gödel tétel bizonyítása. 




