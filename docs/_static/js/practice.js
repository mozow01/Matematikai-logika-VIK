(() => {
  'use strict';

  const evaluationTasks = [
    {
      expression: `Ite (Ite Fal Fal Tru)
    (Ite Fal Tru Fal)
    (Ite Tru Tru Fal)`,
      answers: {
        condition: 'Tru',
        branch: 'then',
        result: 'Fal',
        denotation: 'false',
        sameSyntax: 'no',
      },
      explanation:
        'A feltételként álló Ite a különben-ágát választja, ezért Tru-ra redukálódik. ' +
        'A külső Ite így az akkor-ágat választja: Ite Fal Tru Fal, ennek eredménye Fal. ' +
        'A denotáció false. Az eredeti Ite-fa és a Fal levél nem ugyanaz a szintaxisfa.',
    },
    {
      expression: `Ite (Neg (Ite Tru Fal Tru))
    Tru
    (And2 Tru Fal)`,
      answers: {
        condition: 'Tru',
        branch: 'then',
        result: 'Tru',
        denotation: 'true',
        sameSyntax: 'no',
      },
      explanation:
        'Ite Tru Fal Tru eredménye Fal, ezért Neg Fal eredménye Tru. ' +
        'A külső Ite az akkor-ágat választja, amely már Tru. A denotáció true, ' +
        'de az eredeti összetett fa szintaktikusan nem a Tru konstruktor.',
    },
    {
      expression: `And (Neg Fal)
    (Ite Fal Tru (Neg Tru))`,
      answers: {
        condition: 'Tru',
        branch: 'then',
        result: 'Fal',
        denotation: 'false',
        sameSyntax: 'no',
      },
      explanation:
        'Az And definícióját kibontva a legkülső feltétel Neg Fal, ami Tru. ' +
        'Az akkor-ágban előbb a második argumentumot értékeljük: ' +
        'Ite Fal Tru (Neg Tru) eredménye Fal. Így Ite Fal Tru Fal, majd Fal adódik. ' +
        'A denotáció false; az összetett And-kifejezés nem ugyanaz a szintaxisfa, mint Fal.',
    },
    {
      expression: `Ite (And2 Tru (Neg Tru))
    (Neg Fal)
    (And2 (Neg Fal) Tru)`,
      answers: {
        condition: 'Fal',
        branch: 'else',
        result: 'Tru',
        denotation: 'true',
        sameSyntax: 'no',
      },
      explanation:
        'A feltétel And2 Tru (Neg Tru). Neg Tru eredménye Fal, ezért a teljes feltétel Fal. ' +
        'A külső Ite a különben-ágat választja. Ott Neg Fal eredménye Tru, ' +
        'így And2 Tru Tru eredménye Tru. A denotáció true, a két szintaxisfa azonban különböző.',
    },
  ];

  const programCandidates = [
    {
      id: 'or',
      body: 'Ite A Tru B',
      values: [false, true, true, true],
    },
    {
      id: 'impl',
      body: 'Ite A B Tru',
      values: [true, true, false, true],
    },
    {
      id: 'xor',
      body: 'Ite A (Neg B) B',
      values: [false, true, true, false],
    },
    {
      id: 'eqv',
      body: 'Ite A B (Neg B)',
      values: [true, false, false, true],
    },
  ];

  const programTasks = [
    {
      name: 'diszjunkció',
      description: 'Az eredmény akkor Tru, ha A és B közül legalább az egyik Tru.',
      correct: 'or',
      values: [false, true, true, true],
    },
    {
      name: 'implikáció',
      description: 'Az eredmény csak A = Tru és B = Fal esetén Fal.',
      correct: 'impl',
      values: [true, true, false, true],
    },
    {
      name: 'kizáró vagy',
      description: 'Az eredmény pontosan akkor Tru, ha A és B különbözik.',
      correct: 'xor',
      values: [false, true, true, false],
    },
    {
      name: 'ekvivalencia',
      description: 'Az eredmény pontosan akkor Tru, ha A és B megegyezik.',
      correct: 'eqv',
      values: [true, false, false, true],
    },
  ];

  const fieldDefinitions = [
    {
      name: 'condition',
      label: 'Mire redukálódik a legkülső Ite feltétele?',
      options: [['Tru', 'Tru'], ['Fal', 'Fal']],
    },
    {
      name: 'branch',
      label: 'Melyik ágat kell ezután kiértékelni?',
      options: [['then', 'akkor-ág (2. argumentum)'], ['else', 'különben-ág (3. argumentum)']],
    },
    {
      name: 'result',
      label: 'Mi a teljes beta_reduce eredménye?',
      options: [['Tru', 'Tru'], ['Fal', 'Fal']],
    },
    {
      name: 'denotation',
      label: 'Mi a teljes kifejezés denote eredménye?',
      options: [['true', 'true'], ['false', 'false']],
    },
    {
      name: 'sameSyntax',
      label: 'Az eredeti kifejezés és a redukált eredmény ugyanaz a szintaxisfa?',
      options: [['yes', 'igen'], ['no', 'nem']],
    },
  ];

  const truthInputs = [
    ['Fal', 'Fal'],
    ['Fal', 'Tru'],
    ['Tru', 'Fal'],
    ['Tru', 'Tru'],
  ];

  function randomIndex(length) {
    if (globalThis.crypto?.getRandomValues) {
      const values = new Uint32Array(1);
      globalThis.crypto.getRandomValues(values);
      return values[0] % length;
    }
    return Math.floor(Math.random() * length);
  }

  function differentIndex(length, previous) {
    if (length < 2 || previous === null) return randomIndex(length);
    let next = randomIndex(length - 1);
    if (next >= previous) next += 1;
    return next;
  }

  function shuffled(items) {
    const copy = [...items];
    for (let i = copy.length - 1; i > 0; i -= 1) {
      const j = randomIndex(i + 1);
      [copy[i], copy[j]] = [copy[j], copy[i]];
    }
    return copy;
  }

  function boolName(value) {
    return value ? 'Tru' : 'Fal';
  }

  function appendTextElement(parent, tagName, text, className = '') {
    const element = document.createElement(tagName);
    element.textContent = text;
    if (className) element.className = className;
    parent.append(element);
    return element;
  }

  function createTruthTable(task) {
    const table = document.createElement('table');
    table.className = 'docutils align-default truth-table';
    const head = table.createTHead().insertRow();
    ['A', 'B', 'eredmény'].forEach(label => {
      const cell = document.createElement('th');
      cell.scope = 'col';
      cell.textContent = label;
      head.append(cell);
    });

    const body = table.createTBody();
    truthInputs.forEach(([a, b], index) => {
      const row = body.insertRow();
      [a, b, boolName(task.values[index])].forEach(value => {
        const cell = row.insertCell();
        cell.textContent = value;
      });
    });
    return table;
  }

  function setFeedback(element, kind, messages) {
    element.className = `practice-feedback is-${kind}`;
    element.replaceChildren();
    messages.forEach((message, index) => {
      const paragraph = document.createElement('p');
      paragraph.textContent = message;
      if (index === 0) {
        const strong = document.createElement('strong');
        strong.textContent = kind === 'success' ? 'Helyes. ' : 'Nézd meg még egyszer. ';
        paragraph.prepend(strong);
      }
      element.append(paragraph);
    });
  }

  function clearFeedback(element) {
    element.className = 'practice-feedback';
    element.replaceChildren();
  }

  function firstProgramMismatch(task, candidate) {
    const mismatch = task.values.findIndex((value, index) => value !== candidate.values[index]);
    if (mismatch === -1) return '';
    const [a, b] = truthInputs[mismatch];
    return `A = ${a}, B = ${b} esetén a választott kód ${boolName(candidate.values[mismatch])}-t ad, ` +
      `pedig ${boolName(task.values[mismatch])} kellene.`;
  }

  function initialisePractice(mount) {
    mount.replaceChildren();
    appendTextElement(
      mount,
      'p',
      'Minden változat két, egymástól független feladatot ad. A válaszokat az oldal nem menti és nem küldi el.',
      'practice-intro',
    );

    const evaluationCard = document.createElement('section');
    evaluationCard.className = 'practice-card';
    evaluationCard.setAttribute('aria-labelledby', 'evaluation-title');
    appendTextElement(evaluationCard, 'h3', '1. Kiértékelési lánc', '').id = 'evaluation-title';
    appendTextElement(
      evaluationCard,
      'p',
      'Bontsd ki a Neg, And és And2 definícióját, ha szükséges, majd kövesd a kiválasztott ágakat.',
    );
    const expression = appendTextElement(evaluationCard, 'pre', '', 'practice-expression');
    const evaluationForm = document.createElement('div');
    evaluationForm.className = 'practice-fields';
    evaluationCard.append(evaluationForm);
    const evaluationFeedback = document.createElement('div');
    evaluationFeedback.className = 'practice-feedback';
    evaluationFeedback.setAttribute('role', 'status');
    evaluationFeedback.setAttribute('aria-live', 'polite');
    evaluationCard.append(evaluationFeedback);

    const programCard = document.createElement('section');
    programCard.className = 'practice-card';
    programCard.setAttribute('aria-labelledby', 'program-title');
    appendTextElement(programCard, 'h3', '2. Programválasztás', '').id = 'program-title';
    const programDescription = appendTextElement(programCard, 'p', '');
    const truthTableHolder = document.createElement('div');
    programCard.append(truthTableHolder);
    const options = document.createElement('fieldset');
    options.className = 'practice-options';
    const legend = document.createElement('legend');
    legend.textContent = 'Melyik definíció valósítja meg ezt a műveletet?';
    options.append(legend);
    programCard.append(options);
    const programFeedback = document.createElement('div');
    programFeedback.className = 'practice-feedback';
    programFeedback.setAttribute('role', 'status');
    programFeedback.setAttribute('aria-live', 'polite');
    programCard.append(programFeedback);

    mount.append(evaluationCard, programCard);

    const help = document.createElement('details');
    help.className = 'practice-help';
    const helpSummary = document.createElement('summary');
    helpSummary.textContent = 'Segítség a megoldáshoz';
    help.append(helpSummary);
    const helpList = document.createElement('ol');
    [
      'Először bontsd ki a származtatott műveleteket: Neg, And vagy And2.',
      'Mindig a legkülső Ite feltételét értékeld ki először.',
      'Tru feltételnél a második, Fal feltételnél a harmadik argumentummal folytasd.',
      'A programválasztásnál próbáld ki mind a négy Tru/Fal bemenetpárt.',
    ].forEach(item => appendTextElement(helpList, 'li', item));
    help.append(helpList);
    mount.append(help);

    const actions = document.createElement('div');
    actions.className = 'practice-actions';
    const checkButton = appendTextElement(actions, 'button', 'Ellenőrzés', 'practice-button');
    checkButton.type = 'button';
    const anotherButton = appendTextElement(actions, 'button', 'Másik változat', 'practice-button practice-button--secondary');
    anotherButton.type = 'button';
    const resetButton = appendTextElement(actions, 'button', 'Válaszok törlése', 'practice-button practice-button--secondary');
    resetButton.type = 'button';
    mount.append(actions);

    let evaluationIndex = null;
    let programIndex = null;

    function renderEvaluation() {
      const task = evaluationTasks[evaluationIndex];
      expression.textContent = task.expression;
      evaluationForm.replaceChildren();
      fieldDefinitions.forEach(field => {
        const wrapper = document.createElement('label');
        wrapper.className = 'practice-field';
        const label = document.createElement('span');
        label.textContent = field.label;
        const select = document.createElement('select');
        select.name = field.name;
        select.setAttribute('aria-label', field.label);
        const placeholder = document.createElement('option');
        placeholder.value = '';
        placeholder.textContent = 'Válassz…';
        select.append(placeholder);
        shuffled(field.options).forEach(([value, text]) => {
          const option = document.createElement('option');
          option.value = value;
          option.textContent = text;
          select.append(option);
        });
        wrapper.append(label, select);
        evaluationForm.append(wrapper);
      });
      clearFeedback(evaluationFeedback);
    }

    function renderProgram() {
      const task = programTasks[programIndex];
      programDescription.textContent = `${task.name[0].toUpperCase()}${task.name.slice(1)}: ${task.description}`;
      truthTableHolder.replaceChildren(createTruthTable(task));
      options.querySelectorAll('label').forEach(label => label.remove());
      shuffled(programCandidates).forEach(candidate => {
        const label = document.createElement('label');
        label.className = 'practice-option';
        const radio = document.createElement('input');
        radio.type = 'radio';
        radio.name = 'program-choice';
        radio.value = candidate.id;
        const code = document.createElement('code');
        code.textContent = `Definition Op (A B : Boole) : Boole :=\n  ${candidate.body}.`;
        label.append(radio, code);
        options.append(label);
      });
      clearFeedback(programFeedback);
    }

    function selectNewTasks() {
      evaluationIndex = differentIndex(evaluationTasks.length, evaluationIndex);
      programIndex = differentIndex(programTasks.length, programIndex);
      renderEvaluation();
      renderProgram();
    }

    function resetAnswers() {
      evaluationForm.querySelectorAll('select').forEach(select => { select.value = ''; });
      options.querySelectorAll('input').forEach(input => { input.checked = false; });
      clearFeedback(evaluationFeedback);
      clearFeedback(programFeedback);
    }

    function checkEvaluation() {
      const task = evaluationTasks[evaluationIndex];
      const controls = [...evaluationForm.querySelectorAll('select')];
      const missing = controls.find(control => !control.value);
      if (missing) {
        setFeedback(evaluationFeedback, 'error', ['Töltsd ki mind az öt mezőt.']);
        missing.focus();
        return false;
      }

      const incorrect = fieldDefinitions.filter(field => {
        const value = evaluationForm.querySelector(`[name="${field.name}"]`).value;
        return value !== task.answers[field.name];
      });

      if (incorrect.length === 0) {
        setFeedback(evaluationFeedback, 'success', [task.explanation]);
        return true;
      }

      setFeedback(evaluationFeedback, 'error', [
        `A javítandó sorok száma: ${incorrect.length}.`,
        task.explanation,
      ]);
      return false;
    }

    function checkProgram() {
      const task = programTasks[programIndex];
      const selected = options.querySelector('input:checked');
      if (!selected) {
        setFeedback(programFeedback, 'error', ['Válassz egy definíciót.']);
        options.querySelector('input')?.focus();
        return false;
      }

      const candidate = programCandidates.find(item => item.id === selected.value);
      if (candidate.id === task.correct) {
        setFeedback(programFeedback, 'success', [
          `A(z) ${candidate.body} mind a négy bemenetpárnál a megadott értéket adja.`,
        ]);
        return true;
      }

      const correct = programCandidates.find(item => item.id === task.correct);
      setFeedback(programFeedback, 'error', [
        firstProgramMismatch(task, candidate),
        `A megfelelő törzs: ${correct.body}.`,
      ]);
      return false;
    }

    checkButton.addEventListener('click', () => {
      const evaluationCorrect = checkEvaluation();
      const programCorrect = checkProgram();
      if (evaluationCorrect && programCorrect) {
        checkButton.textContent = 'Minden válasz helyes';
      } else {
        checkButton.textContent = 'Újraellenőrzés';
      }
    });

    anotherButton.addEventListener('click', () => {
      selectNewTasks();
      checkButton.textContent = 'Ellenőrzés';
      evaluationCard.scrollIntoView({ behavior: 'smooth', block: 'start' });
    });

    resetButton.addEventListener('click', () => {
      resetAnswers();
      checkButton.textContent = 'Ellenőrzés';
    });

    selectNewTasks();
  }

  window.addEventListener('DOMContentLoaded', () => {
    document.querySelectorAll('[data-boole-practice]').forEach(initialisePractice);
  });
})();
