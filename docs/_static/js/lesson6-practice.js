(() => {
  "use strict";

  const tasks = {
    "disjunction-tree": {
      answer: "correct",
      options: [
        {
          value: "correct",
          text: "A ∨ B    [A] ⟶ B ∨ A (∨I₂)    [B] ⟶ B ∨ A (∨I₁)\n────────────────────────────────────────────── ∨E\n                    B ∨ A",
        },
        {
          value: "wrong-left",
          text: "A ∨ B    [A] ⟶ B ∨ A (∨I₁)    [B] ⟶ B ∨ A (∨I₂)\n────────────────────────────────────────────── ∨E\n                    B ∨ A",
        },
        {
          value: "wrong-no-case",
          text: "A ∨ B\n────── ∨I₁\nB ∨ A",
        },
      ],
      success: "Helyes. Az A ágban a jobb, a B ágban a bal oldalt vezetjük be, majd a két ágat a ∨E egyesíti.",
      retry: "Nem ez felel meg a kódnak. Figyelje meg, melyik ágon használ left, illetve right taktikát.",
    },
    "contraposition-tree": {
      answer: "correct",
      options: [
        {
          value: "correct",
          text: "A → B    [A]\n──────────── →E\n      B       B → ⊥\n      ─────────── →E\n            ⊥\n      ─────────── →I, [A] lezárása\n           A → ⊥",
        },
        {
          value: "wrong-direction",
          text: "B → A    [A]\n──────────── →E\n      B       B → ⊥\n      ─────────── →E\n            ⊥\n      ─────────── →I\n           A → ⊥",
        },
        {
          value: "wrong-conclusion",
          text: "A → B    A\n─────────── →E\n     B\n─────────── →I\n   B → A",
        },
      ],
      success: "Helyes. Az A feltételezésből A → B segítségével B, majd B → ⊥ segítségével ellentmondás keletkezik.",
      retry: "Nem ez a kód levezetése. A ~B jelentése B → False, a végén pedig az A feltételezést kell lezárni.",
    },
    "de-morgan-tree": {
      answer: "correct",
      options: [
        {
          value: "correct",
          text: "[A] ⟶ A ∨ B (∨I₁) ⟶ ⊥, ezért ¬A\n[B] ⟶ A ∨ B (∨I₂) ⟶ ⊥, ezért ¬B\n──────────────────────────────────── ∧I\n                 ¬A ∧ ¬B",
        },
        {
          value: "wrong-connective",
          text: "[A] ⟶ A ∨ B ⟶ ⊥, ezért ¬A\n[B] ⟶ A ∨ B ⟶ ⊥, ezért ¬B\n─────────────────────────────────── ∨I\n                 ¬A ∨ ¬B",
        },
        {
          value: "wrong-premise",
          text: "A ∧ B    ¬(A ∨ B)\n──────────────── →E\n        ¬A ∧ ¬B",
        },
      ],
      success: "Helyes. A két negációt külön bizonyítjuk, majd ∧I segítségével párba rendezzük őket.",
      retry: "Nem ez felel meg a split két ágának. Mindkét ágban diszjunkciót építünk, majd alkalmazzuk a közös H feltételt.",
    },
    "implication-tree": {
      answer: "correct",
      options: [
        {
          value: "correct",
          text: "A ∨ ¬A    [A] ⟶ B (→E) ⟶ ¬A ∨ B (∨I₂)    [¬A] ⟶ ¬A ∨ B (∨I₁)\n────────────────────────────────────────────────────────────── ∨E\n                           ¬A ∨ B",
        },
        {
          value: "wrong-introduction",
          text: "A ∨ ¬A    [A] ⟶ B ⟶ ¬A ∨ B (∨I₁)    [¬A] ⟶ ¬A ∨ B (∨I₂)\n──────────────────────────────────────────────────────── ∨E\n                         ¬A ∨ B",
        },
        {
          value: "wrong-no-decision",
          text: "A → B    [A]\n────────── →E\n     B\n────────── ∨I₂\n   ¬A ∨ B",
        },
      ],
      success: "Helyes. Az eldönthetőségi feltételen választunk esetet: A esetén B-t, ¬A esetén közvetlenül a bal oldalt kapjuk.",
      retry: "Nem ez követi a kódot. A külső esetbontás az A ∨ ~A feltételen történik, és az ágak más-más diszjunkcióoldalt vezetnek be.",
    },
  };

  function shuffled(options) {
    const result = [...options];
    for (let index = result.length - 1; index > 0; index -= 1) {
      const other = Math.floor(Math.random() * (index + 1));
      [result[index], result[other]] = [result[other], result[index]];
    }
    return result;
  }

  function buildPractice(mount, task, index) {
    mount.textContent = "";
    const form = document.createElement("form");
    const fieldset = document.createElement("fieldset");
    const legend = document.createElement("legend");
    const options = document.createElement("div");
    const button = document.createElement("button");
    const feedback = document.createElement("p");

    form.className = "practice-shell";
    legend.textContent = "Válassza ki a megfelelő levezetést.";
    options.className = "practice-options";

    shuffled(task.options).forEach((option) => {
      const label = document.createElement("label");
      const input = document.createElement("input");
      const code = document.createElement("code");

      label.className = "practice-option";
      input.type = "radio";
      input.name = `lesson6-answer-${index}`;
      input.value = option.value;
      code.textContent = option.text;
      label.append(input, code);
      options.append(label);
    });

    button.type = "submit";
    button.className = "practice-button";
    button.textContent = "Ellenőrzés";
    feedback.className = "practice-feedback";
    feedback.setAttribute("role", "status");
    feedback.setAttribute("aria-live", "polite");

    fieldset.append(legend, options);
    form.append(fieldset, button, feedback);
    form.addEventListener("submit", (event) => {
      event.preventDefault();
      const selected = form.querySelector("input:checked");
      const correct = selected && selected.value === task.answer;
      feedback.classList.toggle("is-success", Boolean(correct));
      feedback.classList.toggle("is-error", !correct);
      feedback.textContent = correct ? task.success : task.retry;
    });

    mount.append(form);
  }

  function init() {
    document.querySelectorAll("[data-lesson6-practice]").forEach((mount, index) => {
      const task = tasks[mount.dataset.lesson6Practice];
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
