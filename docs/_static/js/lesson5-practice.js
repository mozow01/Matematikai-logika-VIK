(() => {
  "use strict";

  const tasks = {
    "implication-program": {
      answer: "first",
      options: [
        {
          value: "first",
          code: "fun (A B C D : Prop) (HAB : A -> B) (HBC : B -> C) (HCD : C -> D) (HA : A) => HCD (HBC (HAB HA))",
        },
        {
          value: "second",
          code: "fun (A B C D : Prop) (HA : A) (HAB : A -> B) (HBC : B -> C) (HCD : C -> D) => HCD (HBC (HAB HA))",
        },
        {
          value: "third",
          code: "fun (A B C D : Prop) (HAB : A -> B) (HCD : C -> D) (HBC : B -> C) (HA : A) => HCD (HBC (HAB HA))",
        },
      ],
      success: "Helyes. A program az A bizonyítását egymás után az A -> B, B -> C és C -> D függvényeknek adja át.",
      retry: "Ez a program érvényes, de nem pontosan a megadott típusú. Ellenőrizze a négy feltétel sorrendjét.",
    },
    "conjunction-program": {
      answer: "first",
      options: [
        {
          value: "first",
          code: "fun (A B C : Prop) (HAB : A -> B) (HAC : A -> C) (HA : A) => conj (HAB HA) (HAC HA)",
        },
        {
          value: "second",
          code: "fun (A B C : Prop) (HAB : A -> B) (HAC : A -> C) (HA : A) => conj (HAC HA) (HAB HA)",
        },
        {
          value: "third",
          code: "fun (A B C : Prop) (HAB : A -> B) (HAC : A -> C) => conj HAB HAC",
        },
      ],
      success: "Helyes. Ugyanabból az A bizonyításból készül egy B és egy C bizonyítás, majd a conj ebben a sorrendben párt alkot belőlük.",
      retry: "Ez a program érvényes, de más típust állít elő. Ellenőrizze a paramétereket és a konjunkció tagjainak sorrendjét.",
    },
  };

  function buildPractice(mount, task, index) {
    mount.textContent = "";
    const form = document.createElement("form");
    const fieldset = document.createElement("fieldset");
    const legend = document.createElement("legend");
    const button = document.createElement("button");
    const feedback = document.createElement("p");

    legend.textContent = "Melyik program típusa egyezik a lemmával?";
    fieldset.append(legend);

    task.options.forEach((option, optionIndex) => {
      const row = document.createElement("p");
      const label = document.createElement("label");
      const input = document.createElement("input");
      const code = document.createElement("code");

      input.type = "radio";
      input.name = `lesson5-answer-${index}`;
      input.value = option.value;
      code.textContent = option.code;
      label.append(input, " ", code);
      row.append(label);
      fieldset.append(row);
    });

    button.type = "submit";
    button.textContent = "Ellenőrzés";
    feedback.setAttribute("role", "status");
    feedback.setAttribute("aria-live", "polite");

    form.append(fieldset, button, feedback);
    form.addEventListener("submit", (event) => {
      event.preventDefault();
      const selected = form.querySelector("input:checked");
      const correct = selected && selected.value === task.answer;
      feedback.textContent = correct ? task.success : task.retry;
    });

    mount.append(form);
  }

  function init() {
    document.querySelectorAll("[data-lesson5-practice]").forEach((mount, index) => {
      const task = tasks[mount.dataset.lesson5Practice];
      if (task) {
        buildPractice(mount, task, index);
      }
    });
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();
