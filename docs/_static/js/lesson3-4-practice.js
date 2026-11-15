(() => {
  "use strict";

  const tasks = {
    "tree-evaluation": {
      fields: [
        {
          label: "Az eredményül kapott fa",
          answer: "a",
          options: [
            ["", "Válasszon…"],
            ["a", "node (node leaf leaf) (node leaf (node leaf (node leaf leaf)))"],
            ["b", "node (node leaf (node leaf leaf)) (node leaf (node leaf leaf))"],
            ["c", "node (node leaf leaf) (node (node leaf leaf) (node leaf leaf))"],
          ],
        },
        {
          label: "A levelek száma",
          answer: "6",
          options: [["", "Válasszon…"], ["5", "5"], ["6", "6"], ["7", "7"]],
        },
        {
          label: "A magasság",
          answer: "4",
          options: [["", "Válasszon…"], ["3", "3"], ["4", "4"], ["5", "5"]],
        },
      ],
      success: "Helyes. A rekurzió végig a jobb részfán halad; az eredménynek 6 levele és 4-es magassága van.",
      retry: "Még nem mindhárom válasz helyes. Kövesse az oplus definícióját a p legjobboldalibb leveléig.",
    },
    "tree-proof": {
      fields: [
        {
          label: "[1] A leaf eset",
          answer: "one",
          options: [["", "Válasszon…"], ["one", "- reflexivity."], ["x", "- exact IHr."], ["y", "- exact IHl."]],
        },
        {
          label: "[2] A node eset kezdete",
          answer: "two",
          options: [["", "Válasszon…"], ["x", "- exact IHl."], ["two", "- simpl."], ["y", "- rewrite IHl."]],
        },
        {
          label: "[3] A megfelelő hipotézis",
          answer: "three",
          options: [["", "Válasszon…"], ["x", "rewrite IHl."], ["y", "exact IHr."], ["three", "rewrite IHr."]],
        },
        {
          label: "[4] A lezárás",
          answer: "four",
          options: [["", "Válasszon…"], ["x", "exact IHr."], ["four", "reflexivity."], ["y", "rewrite IHl."]],
        },
      ],
      success: "Helyes. A simpl után csak a jobb részfára vonatkozó IHr írja át a szükséges kifejezést.",
      retry: "A négy sor még nem alkot helyes bizonyítást. Az oplus csak a jobb részfán rekurzív.",
    },
    "ast-evaluation": {
      fields: [
        {
          label: "A lefordított szintaxisfa",
          answer: "a",
          options: [
            ["", "Válasszon…"],
            ["a", "node2 OR_c (leaf 0) (node1 NOT_c (leaf 1))"],
            ["b", "node1 NOT_c (node2 OR_c (leaf 0) (leaf 1))"],
            ["c", "node2 AND_c (leaf 0) (node1 NOT_c (leaf 1))"],
          ],
        },
        {
          label: "A visszafordított kifejezés",
          answer: "a",
          options: [
            ["", "Válasszon…"],
            ["a", "OR (AT 0) (NOT (AT 1))"],
            ["b", "NOT (OR (AT 0) (AT 1))"],
            ["c", "AND (AT 0) (NOT (AT 1))"],
          ],
        },
        {
          label: "A denotáció",
          answer: "false",
          options: [["", "Válasszon…"], ["true", "true"], ["false", "false"]],
        },
      ],
      success: "Helyes. A fordító megőrzi a szerkezetet; false OR (NOT true) értéke false.",
      retry: "Még nem mindhárom válasz helyes. Először a külső konstruktort fordítsa le, majd haladjon befelé.",
    },
    "ast-proof": {
      fields: [
        {
          label: "[1] Az atom esete",
          answer: "one",
          options: [["", "Válasszon…"], ["one", "- reflexivity."], ["x", "- rewrite IH."], ["y", "- destruct b."]],
        },
        {
          label: "[2] Az egyargumentumú csomópont",
          answer: "two",
          options: [
            ["", "Válasszon…"],
            ["x", "- simpl; rewrite IH; reflexivity."],
            ["two", "- destruct u; simpl; rewrite IH; reflexivity."],
            ["y", "- destruct b; reflexivity."],
          ],
        },
        {
          label: "[3] A kétargumentumú művelet felbontása",
          answer: "three",
          options: [["", "Válasszon…"], ["x", "- destruct u."], ["three", "- destruct b."], ["y", "- simpl."]],
        },
        {
          label: "[4] A két keletkező cél",
          answer: "four",
          options: [
            ["", "Válasszon…"],
            ["four", "all: simpl; rewrite IH1, IH2; reflexivity."],
            ["x", "all: simpl; rewrite IH; reflexivity."],
            ["y", "simpl; rewrite IH1; reflexivity."],
          ],
        },
      ],
      success: "Helyes. Az u és b műveletkódokat felbontjuk, majd a részfák indukciós hipotéziseivel írunk át.",
      retry: "A négy sor még nem alkot helyes bizonyítást. Vegye figyelembe, hogy UnOp és BinOp értékekre is esetbontás kell.",
    },
  };

  function addField(form, field, index) {
    const row = document.createElement("p");
    const label = document.createElement("label");
    const select = document.createElement("select");
    const id = `course-practice-${form.dataset.task}-${index}`;

    label.htmlFor = id;
    label.textContent = `${field.label}: `;
    select.id = id;
    select.dataset.answer = field.answer;

    field.options.forEach(([value, optionText]) => {
      const option = document.createElement("option");
      option.value = value;
      option.textContent = optionText;
      select.append(option);
    });

    row.append(label, select);
    form.append(row);
  }

  function buildPractice(mount, key, task) {
    mount.textContent = "";
    const form = document.createElement("form");
    const button = document.createElement("button");
    const feedback = document.createElement("p");

    form.dataset.task = key;
    task.fields.forEach((field, index) => addField(form, field, index));

    button.type = "submit";
    button.textContent = "Ellenőrzés";
    feedback.setAttribute("role", "status");
    feedback.setAttribute("aria-live", "polite");

    form.append(button, feedback);
    form.addEventListener("submit", (event) => {
      event.preventDefault();
      const selects = [...form.querySelectorAll("select")];
      const correct = selects.every((select) => {
        const fieldIsCorrect = select.value === select.dataset.answer;
        select.setAttribute("aria-invalid", String(!fieldIsCorrect));
        return fieldIsCorrect;
      });
      feedback.textContent = correct ? task.success : task.retry;
    });

    mount.append(form);
  }

  function init() {
    document.querySelectorAll("[data-course-practice]").forEach((mount) => {
      const key = mount.dataset.coursePractice;
      if (tasks[key]) {
        buildPractice(mount, key, tasks[key]);
      }
    });
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();
