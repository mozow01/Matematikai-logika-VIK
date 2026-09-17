(() => {
  'use strict';

  const categories = [
    {
      id: 'beta',
      title: 'Háromszintű béta-redukció',
      description: 'Kövesd belülről kifelé, hogy az egymásba ágyazott Ite-k melyik ágat választják.',
      variants: [
        {
          id: 'A',
          label: 'Tru / Fal / Fal',
          key: 'practice_beta_2',
          theorem: `Theorem beta_nested_tff :
  forall A B C D E F G,
    beta_reduce A = Tru ->
    beta_reduce B = Fal ->
    beta_reduce E = Fal ->
    beta_reduce (Ite (Ite (Ite A B C) D E) F G) = beta_reduce G.`,
          motivation:
            'Itt kétszer is irányt váltunk. Ez segít elválasztani a kifejezés fájának helyét attól, hogy az adott feltétel melyik ágat engedi tovább.',
          success:
            'Az útvonal: A kiválasztja B-t, B = Fal ezért E következik, E = Fal ezért végül G. A jsCoq-ban ezt a három döntést kell igazolnod.',
          questions: [
            {
              id: 'inner',
              kind: 'select',
              prompt: 'Mire redukálódik a legbelső Ite A B C?',
              options: [
                ['b', 'beta_reduce B, mert A Tru-ra redukálódik'],
                ['c', 'C, mert B Fal-ra redukálódik'],
                ['a', 'A, mert ez a feltétel'],
              ],
              answer: 'b',
              hint: 'Előbb csak a feltételt nézd: A Tru, tehát az akkor-ágat választjuk.',
            },
            {
              id: 'middle',
              kind: 'select',
              prompt: 'Mire redukálódik ezután az Ite (Ite A B C) D E?',
              options: [
                ['d', 'beta_reduce D'],
                ['e', 'beta_reduce E'],
                ['b', 'beta_reduce B'],
              ],
              answer: 'e',
              hint: 'Fal feltételnél a harmadik argumentum, a különben-ág marad.',
            },
            {
              id: 'outer',
              kind: 'select',
              prompt: 'Mi lesz a teljes kifejezés eredménye?',
              options: [
                ['f', 'beta_reduce F'],
                ['g', 'beta_reduce G'],
                ['e', 'beta_reduce E'],
              ],
              answer: 'g',
              hint: 'Minden Ite a saját, teljes feltételének redukált értékét vizsgálja.',
            },
          ],
        },
        {
          id: 'B',
          label: 'Fal / Fal / Tru',
          key: 'practice_beta_4',
          theorem: `Theorem beta_nested_fft :
  forall A B C D E F G,
    beta_reduce A = Fal ->
    beta_reduce C = Fal ->
    beta_reduce E = Tru ->
    beta_reduce (Ite (Ite (Ite A B C) D E) F G) = beta_reduce F.`,
          motivation:
            'Ez a változat megmutatja, hogy a három egymásba ágyazott döntésben a különben-ágon át is visszajuthatunk a legkülső akkor-ághoz.',
          success:
            'Az útvonal: A = Fal miatt C következik, C = Fal miatt E, E = Tru miatt pedig F. A jsCoq-ban ugyanezt az útvonalat tedd ellenőrizhetővé.',
          questions: [
            {
              id: 'inner',
              kind: 'select',
              prompt: 'Mire redukálódik a legbelső Ite A B C?',
              options: [
                ['b', 'beta_reduce B'],
                ['c', 'beta_reduce C'],
                ['a', 'beta_reduce A'],
              ],
              answer: 'c',
              hint: 'A Fal feltétel a különben-ágat, vagyis C-t választja.',
            },
            {
              id: 'middle',
              kind: 'select',
              prompt: 'Mire redukálódik ezután az Ite (Ite A B C) D E?',
              options: [
                ['d', 'beta_reduce D'],
                ['e', 'beta_reduce E'],
                ['c', 'beta_reduce C'],
              ],
              answer: 'e',
              hint: 'Az előző feltétel beta_reduce C, amely a hipotézis szerint Fal.',
            },
            {
              id: 'outer',
              kind: 'select',
              prompt: 'Mi lesz a teljes kifejezés eredménye?',
              options: [
                ['f', 'beta_reduce F'],
                ['g', 'beta_reduce G'],
                ['e', 'beta_reduce E'],
              ],
              answer: 'f',
              hint: 'A legkülső feltétel E-re jut, E pedig Tru-ra redukálódik.',
            },
          ],
        },
      ],
    },
    {
      id: 'connective',
      title: 'Származtatott műveletek denotációja',
      description: 'Olvasd ki egy Ite-kódolás igazságfüggvényét, és hasonlítsd össze a Coq bool-műveletével.',
      variants: [
        {
          id: 'A',
          label: 'Kizáró vagy',
          key: 'practice_connective_3',
          theorem: `Theorem ite_xor_denote :
  forall A B,
    denote (Ite A (Neg B) B) =
    xorb (denote A) (denote B).`,
          motivation:
            'A kizáró vagy jó programválasztási próba: nem elég azt tudni, hogy „vagy”, azt is kódolni kell, hogy az azonos bemenetek hamis eredményt adnak.',
          success:
            'Az Ite A (Neg B) B pontosan az F, T, T, F sort adja. A jsCoq-bizonyításban ezt a négy denotációs esetet kell lefedned.',
          questions: [
            {
              id: 'program',
              kind: 'radio',
              prompt: 'Melyik program valósítja meg a kizáró vagy műveletét?',
              options: [
                ['xor', 'Ite A (Neg B) B'],
                ['eqv', 'Ite A B (Neg B)'],
                ['or', 'Ite A Tru B'],
              ],
              answer: 'xor',
              hint: 'Ha A igaz, B ellentettje kell; ha A hamis, B változatlan értéke kell.',
            },
            {
              id: 'truth-table',
              kind: 'select',
              prompt: 'Melyik eredménysor tartozik az (F,F), (F,T), (T,F), (T,T) bemenetekhez?',
              options: [
                ['fttf', 'Fal, Tru, Tru, Fal'],
                ['tfft', 'Tru, Fal, Fal, Tru'],
                ['fttt', 'Fal, Tru, Tru, Tru'],
              ],
              answer: 'fttf',
              hint: 'A kizáró vagy pontosan a különböző bemeneteknél igaz.',
            },
            {
              id: 'proof-cases',
              kind: 'radio',
              prompt: 'Mely esetekre bontás ellenőrzi közvetlenül a teljes igazságtáblát?',
              options: [
                ['both', 'denote A és denote B bool értékei szerint'],
                ['syntax-a', 'csak A szintaxisfája szerint'],
                ['beta', 'csak beta_reduce A eredménye szerint'],
              ],
              answer: 'both',
              hint: 'Két bool érték két-két esete adja a négy igazságtábla-sort.',
            },
          ],
        },
        {
          id: 'B',
          label: 'Ekvivalencia',
          key: 'practice_connective_4',
          theorem: `Theorem ite_eqv_denote :
  forall A B,
    denote (Ite A B (Neg B)) =
    Bool.eqb (denote A) (denote B).`,
          motivation:
            'Az ekvivalencia két program azonos viselkedését teszteli: akkor ad belépőt, ha a két bemenet ugyanahhoz az igazságértékhez tartozik.',
          success:
            'Az Ite A B (Neg B) eredménysora T, F, F, T, ugyanaz, mint a Bool.eqb-é. A jsCoq-ban ezt a négy sort kell tanúsítanod.',
          questions: [
            {
              id: 'program',
              kind: 'radio',
              prompt: 'Melyik program valósítja meg az ekvivalenciát?',
              options: [
                ['eqv', 'Ite A B (Neg B)'],
                ['xor', 'Ite A (Neg B) B'],
                ['and', 'Ite A B Fal'],
              ],
              answer: 'eqv',
              hint: 'Igaz A mellett B-t, hamis A mellett B negációját kell visszaadni.',
            },
            {
              id: 'truth-table',
              kind: 'select',
              prompt: 'Melyik eredménysor tartozik az (F,F), (F,T), (T,F), (T,T) bemenetekhez?',
              options: [
                ['tfft', 'Tru, Fal, Fal, Tru'],
                ['fttf', 'Fal, Tru, Tru, Fal'],
                ['ffft', 'Fal, Fal, Fal, Tru'],
              ],
              answer: 'tfft',
              hint: 'Az ekvivalencia az azonos bemeneteknél igaz.',
            },
            {
              id: 'operator',
              kind: 'radio',
              prompt: 'Melyik Coq bool-művelet írja le ugyanezt az igazságfüggvényt?',
              options: [
                ['eqb', 'Bool.eqb'],
                ['xorb', 'xorb'],
                ['orb', 'orb'],
              ],
              answer: 'eqb',
              hint: 'A bool egyenlőségvizsgáló pontosan az azonos értékeknél ad true-t.',
            },
          ],
        },
      ],
    },
  ];

  // A 3. és 4. feladatcsoport szándékosan rejtve marad a forrásban.
  // Visszakapcsoláskor a két objektumot tedd vissza a categories tömbbe.
  const hiddenCategories = [
    {
      id: 'denotation',
      title: 'Denotációs azonosságok',
      description: 'Azonos jelentést bizonyítunk akkor is, amikor a Boole-szintaxisfák nem azonosak.',
      variants: [
        {
          id: 'A',
          label: 'A konjunkció asszociativitása',
          key: 'practice_denotation_3',
          theorem: `Theorem and2_assoc_denote :
  forall A B C,
    denote (And2 (And2 A B) C) =
    denote (And2 A (And2 B C)).`,
          motivation:
            'A zárójelezés megváltoztatja a program szintaxisfáját, de nem változtatja meg a három bemenetből kiszámolt igazságértéket. A tétel ezt a megfigyelhető azonosságot rögzíti.',
          success:
            'Mindkét oldal pontosan akkor true, ha A, B és C denotációja is true. A három bool érték nyolc esetében ezért ugyanazt kapjuk.',
          questions: [
            {
              id: 'plan',
              kind: 'radio',
              prompt: 'Melyik bizonyítási terv illeszkedik közvetlenül ehhez a denotációs azonossághoz?',
              options: [
                ['truth', 'Az And2 kibontása után esetbontás denote A, denote B és denote C értékére'],
                ['syntax', 'Bizonyítsuk, hogy a két And2-kifejezés ugyanaz a szintaxisfa'],
                ['beta', 'Használjuk kötelezően a normalizációs tételt'],
              ],
              answer: 'truth',
              hint: 'A cél bool értékek egyenlősége; ezek véges esetei közvetlenül ellenőrizhetők.',
            },
            {
              id: 'true-case',
              kind: 'select',
              prompt: 'Mikor true mindkét oldal?',
              options: [
                ['all', 'Ha denote A, denote B és denote C mind true'],
                ['any', 'Ha a három közül legalább egy true'],
                ['outer', 'Ha csak denote A és denote C true'],
              ],
              answer: 'all',
              hint: 'Mindkét zárójelezés háromtagú konjunkciót jelent.',
            },
            {
              id: 'case-count',
              kind: 'radio',
              prompt: 'Legfeljebb hány bool-kombinációt ad a három denotáció szerinti teljes esetbontás?',
              options: [
                ['8', '8 esetet'],
                ['6', '6 esetet'],
                ['27', '27 esetet'],
              ],
              answer: '8',
              hint: 'Mindhárom bool érték kétféle lehet: 2 · 2 · 2.',
            },
          ],
        },
        {
          id: 'B',
          label: 'De Morgan-azonosság',
          key: 'practice_denotation_4',
          theorem: `Theorem de_morgan_denote :
  forall A B,
    denote (Neg (And2 A B)) =
    denote (Ite (Neg A) Tru (Neg B)).`,
          motivation:
            'De Morgan törvénye itt nem külső axióma: két végrehajtható Boole-program azonos viselkedéseként ellenőrizhető.',
          success:
            'Mindkét oldal csak A = true és B = true esetén false. Az And2 és Neg kibontása után a két denotáció négy bool-esetben összevethető.',
          questions: [
            {
              id: 'plan',
              kind: 'radio',
              prompt: 'Melyik bizonyítási terv vizsgálja pontosan a tétel szemantikai tartalmát?',
              options: [
                ['truth', 'A Neg és And2 kibontása, majd esetbontás denote A és denote B értékére'],
                ['same-tree', 'A két Boole-kifejezés szintaktikai egyenlőségének bizonyítása'],
                ['a-only', 'Esetbontás csak denote A értékére, B vizsgálata nélkül'],
              ],
              answer: 'truth',
              hint: 'A két oldal eltérő szintaxisú, de a négy bool bemenetpáron összevethető.',
            },
            {
              id: 'false-row',
              kind: 'select',
              prompt: 'Melyik bemenetpárnál false mindkét oldal?',
              options: [
                ['tt', 'denote A = true és denote B = true'],
                ['tf', 'denote A = true és denote B = false'],
                ['ft', 'denote A = false és denote B = true'],
                ['ff', 'denote A = false és denote B = false'],
              ],
              answer: 'tt',
              hint: 'A „nem (A és B)” pontosan akkor hamis, ha mindkettő igaz.',
            },
            {
              id: 'claim',
              kind: 'radio',
              prompt: 'Mit igazol az egyenlőség ebben a tételben?',
              options: [
                ['meaning', 'A két eltérő kifejezés jelentése minden A és B mellett azonos'],
                ['syntax', 'A két kifejezés ugyanaz a Boole-szintaxisfa'],
                ['beta', 'A beta_reduce függvény egy lépésben ugyanazt adja'],
              ],
              answer: 'meaning',
              hint: 'Mindkét oldalon a denote eredménye szerepel, nem maguk a szintaxisfák.',
            },
          ],
        },
      ],
    },
    {
      id: 'syntax',
      title: 'Szintaxis és szemantika',
      description: 'Válaszd külön a konstruktorok különbözőségét és a kifejezések azonos jelentését.',
      variants: [
        {
          id: 'A',
          label: 'Beágyazott állandó igaz',
          key: 'practice_syntax_2',
          theorem: `Theorem nested_true_branches :
  forall A B,
    Ite A (Ite B Tru Tru) Tru <> Tru /\\
    denote (Ite A (Ite B Tru Tru) Tru) = denote Tru.`,
          motivation:
            'A beágyazás megmutatja, hogy tetszőlegesen összetett vezérlési szerkezet is viselkedhet állandó programként anélkül, hogy szintaktikailag állandó lenne.',
          success:
            'A külső gyökér Ite, ezért nem Tru. A denotáció viszont minden A- és B-értéknél true, mert minden elérhető levél Tru.',
          questions: [
            {
              id: 'outer-shape',
              kind: 'radio',
              prompt: 'Igaz vagy hamis az első rész: Ite A (Ite B Tru Tru) Tru = Tru?',
              options: [
                ['false', 'Hamis: a bal oldal gyökere Ite, a jobb oldalé Tru'],
                ['true', 'Igaz: minden ág Tru-ra vezet'],
              ],
              answer: 'false',
              hint: 'A konstruktorok különbözőségéhez nem kell kiértékelni A-t vagy B-t.',
            },
            {
              id: 'inner',
              kind: 'select',
              prompt: 'Igaz vagy hamis a második rész: a két oldal denotációja azonos?',
              options: [
                ['true', 'Igaz: mindkét oldal true-t denotál'],
                ['false', 'Hamis: az eltérő szintaxis eltérő denotációt kényszerít ki'],
              ],
              answer: 'true',
              hint: 'A belső és a külső feltételes minden elérhető ága Tru.',
            },
            {
              id: 'first-step',
              kind: 'radio',
              prompt: 'Az A és B bevezetése után mi legyen az első szerkezeti taktikai lépés?',
              options: [
                ['split', 'split – válasszuk szét a /\\ két részcélját'],
                ['left', 'left – válasszuk a bal diszjunktat'],
                ['exists', 'exists Tru – adjunk tanút'],
              ],
              answer: 'split',
              hint: 'A tétel legfelső logikai kapcsolata konjunkció.',
            },
          ],
        },
        {
          id: 'B',
          label: 'Beágyazott konjunkció, állandó hamis',
          key: 'practice_syntax_4',
          theorem: `Theorem nested_and_false :
  forall A B,
    And2 A (And2 B Fal) <> Fal /\\
    denote (And2 A (And2 B Fal)) = denote Fal.`,
          motivation:
            'Egy összetett program minden bemenetre viselkedhet Fal-ként úgy, hogy maga a programfa mégsem egyetlen Fal levél. Ezért kell külön útlevél a szintaxisról és a jelentésről szóló állításokhoz.',
          success:
            'Az And2 kibontva Ite konstruktorral kezdődik, tehát nem Fal. Denotációja mégis mindig false, mert a belső konjunkció egyik tagja Fal, a külső különben-ága pedig szintén Fal.',
          questions: [
            {
              id: 'syntax-equality',
              kind: 'radio',
              prompt: 'Igaz vagy hamis az első rész: And2 A (And2 B Fal) = Fal?',
              options: [
                ['false', 'Hamis: az And2 kibontása után a bal oldal Ite konstruktorral kezdődik'],
                ['true', 'Igaz: minden bemenetre Fal az eredmény'],
              ],
              answer: 'false',
              hint: 'A kiszámolt eredmény nem azonos magának a szintaxisfának az alakjával.',
            },
            {
              id: 'denotation-equality',
              kind: 'select',
              prompt: 'Igaz vagy hamis a második rész: a két oldal denotációja azonos?',
              options: [
                ['true', 'Igaz: mindkét oldal false-t denotál'],
                ['false', 'Hamis: a két szintaxisfa különböző'],
              ],
              answer: 'true',
              hint: 'Az And2 B Fal sosem igaz, ezért a külső And2 sem lehet igaz.',
            },
            {
              id: 'first-step',
              kind: 'radio',
              prompt: 'Az A és B bevezetése után mi legyen az első szerkezeti taktikai lépés?',
              options: [
                ['split', 'split – válasszuk szét a nemegyenlőséget és a denotációs egyenlőséget'],
                ['right', 'right – válasszuk a jobb diszjunktat'],
                ['constructor', 'constructor – építsünk Boole-adatot'],
              ],
              answer: 'split',
              hint: 'A /\\ jel két különböző természetű részcélt kapcsol össze.',
            },
          ],
        },
      ],
    },
  ];

  void hiddenCategories;

  let mountCounter = 0;

  function randomIndex(length) {
    if (globalThis.crypto?.getRandomValues) {
      const value = new Uint32Array(1);
      globalThis.crypto.getRandomValues(value);
      return value[0] % length;
    }
    return Math.floor(Math.random() * length);
  }

  function addText(parent, tagName, text, className = '') {
    const element = document.createElement(tagName);
    element.textContent = text;
    if (className) element.className = className;
    parent.append(element);
    return element;
  }

  function playgroundUrl(base, key) {
    const url = new URL(base, document.baseURI);
    url.searchParams.set('example', key);
    return url.href;
  }

  function clearFeedback(element) {
    element.classList.remove('is-success', 'is-error', 'is-warning', 'is-info');
    element.replaceChildren();
  }

  function setFeedback(element, kind, heading, messages = []) {
    clearFeedback(element);
    element.classList.add(`is-${kind}`);
    addText(element, 'p', heading, 'lesson2-practice__feedback-title');
    if (messages.length) {
      const list = document.createElement('ul');
      messages.forEach(message => addText(list, 'li', message));
      element.append(list);
    }
  }

  function answerFor(question, card) {
    const name = card.dataset.questionPrefix + question.id;
    if (question.kind === 'select') {
      return card.querySelector(`select[name="${name}"]`)?.value || '';
    }
    return card.querySelector(`input[name="${name}"]:checked`)?.value || '';
  }

  function questionControl(question, prefix) {
    const fieldset = document.createElement('fieldset');
    fieldset.className = 'lesson2-practice__question';
    fieldset.dataset.questionId = question.id;

    const legend = document.createElement('legend');
    legend.textContent = question.prompt;
    fieldset.append(legend);

    const name = prefix + question.id;
    if (question.kind === 'select') {
      const label = addText(fieldset, 'label', 'Válasz:', 'lesson2-practice__select-label');
      const select = document.createElement('select');
      select.name = name;
      const empty = document.createElement('option');
      empty.value = '';
      empty.textContent = 'Válassz…';
      select.append(empty);
      question.options.forEach(([value, text]) => {
        const option = document.createElement('option');
        option.value = value;
        option.textContent = text;
        select.append(option);
      });
      label.append(select);
    } else {
      const options = document.createElement('div');
      options.className = 'lesson2-practice__options';
      question.options.forEach(([value, text]) => {
        const label = document.createElement('label');
        label.className = 'lesson2-practice__option';
        const radio = document.createElement('input');
        radio.type = 'radio';
        radio.name = name;
        radio.value = value;
        label.append(radio, document.createTextNode(text));
        options.append(label);
      });
      fieldset.append(options);
    }

    return fieldset;
  }

  function initialisePractice(mount) {
    const mountId = ++mountCounter;
    const baseUrl = mount.dataset.jscoqUrl || '../_static/rocq/ite-playground.html';
    const selections = new Map(categories.map(category => [category.id, 0]));
    const cards = new Map();

    mount.classList.add('lesson2-practice');
    mount.replaceChildren();

    const header = document.createElement('header');
    header.className = 'lesson2-practice__header';
    const heading = addText(header, 'h4', '2 × 2 bemelegítő feladatsor');
    heading.id = `lesson2-practice-title-${mountId}`;
    mount.setAttribute('aria-labelledby', heading.id);
    addText(
      header,
      'p',
      'Mindkét látható csoportból válassz egy A vagy B változatot, ahogy a Moodle véletlen kérdéseinél. Itt azonnali, helyi visszajelzést kapsz; a válaszaid nem hagyják el a böngészőt.',
    );

    const toolbar = document.createElement('div');
    toolbar.className = 'lesson2-practice__toolbar';
    const randomButton = addText(toolbar, 'button', 'Véletlen feladatsor', 'lesson2-practice__button');
    randomButton.type = 'button';
    const checkAllButton = addText(toolbar, 'button', 'Mindkettő ellenőrzése', 'lesson2-practice__button lesson2-practice__button--secondary');
    checkAllButton.type = 'button';
    const resetAllButton = addText(toolbar, 'button', 'Válaszok törlése', 'lesson2-practice__button lesson2-practice__button--quiet');
    resetAllButton.type = 'button';
    header.append(toolbar);
    mount.append(header);

    const overallFeedback = document.createElement('div');
    overallFeedback.className = 'lesson2-practice__feedback lesson2-practice__feedback--overall';
    overallFeedback.setAttribute('role', 'status');
    overallFeedback.setAttribute('aria-live', 'polite');
    overallFeedback.setAttribute('aria-atomic', 'true');
    mount.append(overallFeedback);

    const cardList = document.createElement('div');
    cardList.className = 'lesson2-practice__cards';
    mount.append(cardList);

    function selectedTask(category) {
      return category.variants[selections.get(category.id)];
    }

    function announceSelection(category, task, card) {
      const keyUrl = playgroundUrl(baseUrl, task.key);
      card.dataset.jscoqKey = task.key;
      mount.dataset.jscoqKeys = categories
        .map(item => selectedTask(item).key)
        .join(',');
      mount.dispatchEvent(new CustomEvent('lesson2-practice:variantchange', {
        bubbles: true,
        detail: {
          category: category.id,
          variant: task.id,
          key: task.key,
          url: keyUrl,
        },
      }));
    }

    function renderCard(category, card) {
      const task = selectedTask(category);
      const variantIndex = selections.get(category.id);
      const prefix = `lesson2-${mountId}-${category.id}-${task.id}-`;
      card.dataset.questionPrefix = prefix;
      card.replaceChildren();

      const cardHeader = document.createElement('header');
      cardHeader.className = 'lesson2-practice__card-header';
      const number = categories.findIndex(item => item.id === category.id) + 1;
      addText(cardHeader, 'span', `${number}. csoport`, 'lesson2-practice__eyebrow');
      const title = addText(cardHeader, 'h5', category.title);
      title.id = `lesson2-${mountId}-${category.id}-title`;
      card.setAttribute('aria-labelledby', title.id);
      addText(cardHeader, 'p', category.description);
      card.append(cardHeader);

      const picker = document.createElement('fieldset');
      picker.className = 'lesson2-practice__variant-picker';
      addText(picker, 'legend', 'Változat választása');
      category.variants.forEach((variant, index) => {
        const label = document.createElement('label');
        const radio = document.createElement('input');
        radio.type = 'radio';
        radio.name = `lesson2-${mountId}-${category.id}-variant`;
        radio.value = variant.id;
        radio.checked = index === variantIndex;
        radio.addEventListener('change', () => {
          selections.set(category.id, index);
          renderCard(category, card);
          card.querySelectorAll('.lesson2-practice__variant-picker input')[index]?.focus();
          clearFeedback(overallFeedback);
        });
        const labelText = document.createElement('span');
        labelText.textContent = `${variant.id}: ${variant.label}`;
        label.append(radio, labelText);
        picker.append(label);
      });
      card.append(picker);

      const theoremLabel = addText(card, 'p', `A kiválasztott tétel – ${task.id} változat`, 'lesson2-practice__theorem-label');
      const theorem = document.createElement('pre');
      theorem.className = 'lesson2-practice__theorem';
      theorem.setAttribute('aria-labelledby', theoremLabel.id = `lesson2-${mountId}-${category.id}-theorem-label`);
      addText(theorem, 'code', task.theorem);
      card.append(theorem);

      const motivation = document.createElement('aside');
      motivation.className = 'lesson2-practice__motivation';
      addText(motivation, 'strong', 'Miért érdekes? ');
      motivation.append(document.createTextNode(task.motivation));
      card.append(motivation);

      const form = document.createElement('div');
      form.className = 'lesson2-practice__questions';
      task.questions.forEach(question => form.append(questionControl(question, prefix)));
      card.append(form);

      const actions = document.createElement('div');
      actions.className = 'lesson2-practice__card-actions';
      const checkButton = addText(actions, 'button', 'Válaszok ellenőrzése', 'lesson2-practice__button');
      checkButton.type = 'button';
      const clearButton = addText(actions, 'button', 'Törlés', 'lesson2-practice__button lesson2-practice__button--quiet');
      clearButton.type = 'button';
      const jscoqLink = addText(actions, 'a', 'Folytatás jsCoq-ban', 'lesson2-practice__jscoq-link');
      jscoqLink.href = playgroundUrl(baseUrl, task.key);
      jscoqLink.target = '_blank';
      jscoqLink.rel = 'noopener';
      jscoqLink.dataset.jscoqKey = task.key;
      jscoqLink.setAttribute('aria-label', `${category.title}, ${task.id} változat megnyitása jsCoq-ban`);
      actions.append(jscoqLink);
      card.append(actions);

      const feedback = document.createElement('div');
      feedback.className = 'lesson2-practice__feedback';
      feedback.setAttribute('role', 'status');
      feedback.setAttribute('aria-live', 'polite');
      feedback.setAttribute('aria-atomic', 'true');
      card.append(feedback);

      function checkCard(shouldFocus = true) {
        const missing = [];
        const incorrect = [];
        task.questions.forEach((question, index) => {
          const fieldset = form.querySelector(`[data-question-id="${question.id}"]`);
          const answer = answerFor(question, card);
          fieldset.classList.remove('is-correct', 'is-incorrect', 'is-missing');
          if (!answer) {
            missing.push({ question, index, fieldset });
            fieldset.classList.add('is-missing');
          } else if (answer !== question.answer) {
            incorrect.push({ question, index, fieldset });
            fieldset.classList.add('is-incorrect');
          } else {
            fieldset.classList.add('is-correct');
          }
        });

        if (missing.length) {
          setFeedback(
            feedback,
            'warning',
            `Még ${missing.length} kérdésre válaszolnod kell.`,
            incorrect.map(item => `${item.index + 1}. kérdés: ${item.question.hint}`),
          );
          if (shouldFocus) {
            const control = missing[0].fieldset.querySelector('select, input');
            control?.focus();
          }
          return false;
        }

        if (incorrect.length) {
          setFeedback(
            feedback,
            'error',
            `${incorrect.length} választ érdemes újragondolni.`,
            incorrect.map(item => `${item.index + 1}. kérdés: ${item.question.hint}`),
          );
          return false;
        }

        setFeedback(feedback, 'success', 'Mindhárom válasz helyes.', [task.success]);
        return true;
      }

      function clearCard() {
        form.querySelectorAll('select').forEach(select => { select.value = ''; });
        form.querySelectorAll('input[type="radio"]').forEach(radio => { radio.checked = false; });
        form.querySelectorAll('.lesson2-practice__question').forEach(question => {
          question.classList.remove('is-correct', 'is-incorrect', 'is-missing');
        });
        clearFeedback(feedback);
      }

      checkButton.addEventListener('click', () => {
        checkCard();
        clearFeedback(overallFeedback);
      });
      clearButton.addEventListener('click', clearCard);

      card.lesson2Check = checkCard;
      card.lesson2Clear = clearCard;
      announceSelection(category, task, card);
    }

    categories.forEach(category => {
      const card = document.createElement('section');
      card.className = `lesson2-practice__card lesson2-practice__card--${category.id}`;
      cardList.append(card);
      cards.set(category.id, card);
      renderCard(category, card);
    });

    function randomise() {
      categories.forEach(category => {
        selections.set(category.id, randomIndex(category.variants.length));
        renderCard(category, cards.get(category.id));
      });
      clearFeedback(overallFeedback);
      setFeedback(overallFeedback, 'info', 'Új feladatsor készült: mindkét látható csoportból választottunk egy változatot.');
    }

    function clearAll() {
      cards.forEach(card => card.lesson2Clear());
      clearFeedback(overallFeedback);
    }

    randomButton.addEventListener('click', randomise);
    resetAllButton.addEventListener('click', clearAll);
    checkAllButton.addEventListener('click', () => {
      const results = categories.map(category => cards.get(category.id).lesson2Check(false));
      const correct = results.filter(Boolean).length;
      if (correct === categories.length) {
        setFeedback(overallFeedback, 'success', 'A teljes 2 × 2 feladatsor kiválasztott változatai helyesek.');
      } else {
        setFeedback(
          overallFeedback,
          correct ? 'warning' : 'error',
          `${correct} / ${categories.length} csoport kész. A színes jelölések mutatják, hol érdemes folytatni.`,
        );
        cardList.querySelector(
          '.lesson2-practice__question.is-missing select, '
          + '.lesson2-practice__question.is-missing input, '
          + '.lesson2-practice__question.is-incorrect select, '
          + '.lesson2-practice__question.is-incorrect input',
        )?.focus();
      }
    });

    mount.lesson2Practice = {
      getSelection: () => Object.fromEntries(categories.map(category => [category.id, selectedTask(category).key])),
      randomise,
      select(categoryId, variantId) {
        const category = categories.find(item => item.id === categoryId);
        const index = category?.variants.findIndex(item => item.id === variantId) ?? -1;
        if (index < 0) return false;
        selections.set(categoryId, index);
        renderCard(category, cards.get(categoryId));
        return true;
      },
    };
  }

  window.addEventListener('DOMContentLoaded', () => {
    document.querySelectorAll('[data-lesson2-practice]').forEach(initialisePractice);
  });
})();
