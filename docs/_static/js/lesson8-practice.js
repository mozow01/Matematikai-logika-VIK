(() => {
  "use strict";

  const rows = [
    {
      label: "1. levezetés",
      description: "∃E kívül; azon belül ∀I(z), majd ∀I(y), végül ∃I",
      answer: "A",
    },
    {
      label: "2. levezetés",
      description: "∀I(z) kívül; azon belül ∃E, majd ∀I(y), végül ∃I",
      answer: "B",
    },
    {
      label: "3. levezetés",
      description: "∀I(z), majd ∀I(y) kívül; ezeken belül ∃E, végül ∃I",
      answer: "C",
    },
  ];

  function addSelect(row, index) {
    const wrapper = document.createElement("p");
    const label = document.createElement("label");
    const select = document.createElement("select");
    const id = `lesson8-match-${index}`;

    label.htmlFor = id;
    label.textContent = `${row.label}: ${row.description} — `;
    select.id = id;
    select.dataset.answer = row.answer;

    ["", "A", "B", "C"].forEach((value) => {
      const option = document.createElement("option");
      option.value = value;
      option.textContent = value || "Válasszon programot…";
      select.append(option);
    });

    wrapper.append(label, select);
    return wrapper;
  }

  function buildPractice(mount) {
    mount.textContent = "";
    const form = document.createElement("form");
    const fieldset = document.createElement("fieldset");
    const legend = document.createElement("legend");
    const button = document.createElement("button");
    const feedback = document.createElement("p");

    form.className = "practice-shell";
    legend.textContent = "Párosítás";
    rows.forEach((row, index) => fieldset.append(addSelect(row, index)));

    button.type = "submit";
    button.className = "practice-button";
    button.textContent = "Ellenőrzés";
    feedback.className = "practice-feedback";
    feedback.setAttribute("role", "status");
    feedback.setAttribute("aria-live", "polite");

    form.append(fieldset, button, feedback);
    form.addEventListener("submit", (event) => {
      event.preventDefault();
      const selects = [...form.querySelectorAll("select")];
      const selectedValues = selects.map((select) => select.value);
      const allUsedOnce = new Set(selectedValues).size === rows.length &&
        selectedValues.every(Boolean);
      const correct = allUsedOnce && selects.every(
        (select) => select.value === select.dataset.answer,
      );

      selects.forEach((select) => {
        select.setAttribute(
          "aria-invalid",
          String(select.value !== select.dataset.answer),
        );
      });
      feedback.classList.toggle("is-success", correct);
      feedback.classList.toggle("is-error", !correct);
      feedback.textContent = correct
        ? "Helyes párosítás. A destruct H helye mutatja meg, mely univerzális bevezetések vannak az ∃E hatókörén kívül."
        : "A párosítás még nem helyes. Mindegyik programot pontosan egyszer használja, és figyelje a destruct H helyét az intro lépésekhez képest.";
    });

    mount.append(form);
  }

  function init() {
    document.querySelectorAll("[data-lesson8-practice]").forEach((mount) => {
      if (mount.dataset.lesson8Practice === "quantifier-matching") {
        buildPractice(mount);
      }
    });
  }

  if (document.readyState === "loading") {
    document.addEventListener("DOMContentLoaded", init);
  } else {
    init();
  }
})();
