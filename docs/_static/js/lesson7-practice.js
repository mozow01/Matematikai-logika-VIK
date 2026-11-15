(() => {
  "use strict";

  const tasks = {
    "forall-program": {
      answer: "structured",
      options: [
        {
          value: "direct",
          code: `Lemma minden_fa_A : forall (U : Type) (P Q : U -> Prop),
  ((forall x, P x) /\\ (forall x, Q x)) ->
  (forall x, Q x) \\/ (forall x, P x).
Proof.
  intros U P Q H.
  right.
  exact (proj1 H).
Qed.`,
        },
        {
          value: "structured",
          code: `Lemma minden_fa_B : forall (U : Type) (P Q : U -> Prop),
  ((forall x, P x) /\\ (forall x, Q x)) ->
  (forall x, Q x) \\/ (forall x, P x).
Proof.
  intros U P Q H.
  right.
  intro a.
  exact ((proj1 H) a).
Qed.`,
        },
        {
          value: "other-side",
          code: `Lemma minden_fa_C : forall (U : Type) (P Q : U -> Prop),
  ((forall x, P x) /\\ (forall x, Q x)) ->
  (forall x, Q x) \\/ (forall x, P x).
Proof.
  intros U P Q H.
  left.
  intro a.
  exact ((proj2 H) a).
Qed.`,
        },
      ],
      success: "Helyes. A program a jobb oldalt választja, friss a elemet vezet be, majd a konjunkció első univerzális állítását a-ra alkalmazza.",
      retry: "Ez is helyes bizonyítás, de más levezetési szerkezetet követ. Figyelje a ∨I₂, ∀I és ∀E lépések sorrendjét.",
    },
    "exists-program": {
      answer: "structured",
      options: [
        {
          value: "structured",
          code: `Lemma letezik_fa_A : forall (U : Type) (P Q : U -> Prop),
  (exists x, P x /\\ Q x) ->
  (exists x, Q x) \\/ (exists x, P x).
Proof.
  intros U P Q H.
  destruct H as [a Ha].
  right.
  exists a.
  exact (proj1 Ha).
Qed.`,
        },
        {
          value: "right-first",
          code: `Lemma letezik_fa_B : forall (U : Type) (P Q : U -> Prop),
  (exists x, P x /\\ Q x) ->
  (exists x, Q x) \\/ (exists x, P x).
Proof.
  intros U P Q H.
  right.
  destruct H as [a Ha].
  exists a.
  exact (proj1 Ha).
Qed.`,
        },
        {
          value: "other-side",
          code: `Lemma letezik_fa_C : forall (U : Type) (P Q : U -> Prop),
  (exists x, P x /\\ Q x) ->
  (exists x, Q x) \\/ (exists x, P x).
Proof.
  intros U P Q H.
  destruct H as [a Ha].
  left.
  exists a.
  exact (proj2 Ha).
Qed.`,
        },
      ],
      success: "Helyes. A program előbb bontja ki az egzisztenciális feltételt, és csak ezután választja a diszjunkció jobb oldalát.",
      retry: "Ez is helyes bizonyítás, de más fához tartozik. Figyelje az ∃E és a ∨I₂ egymáshoz viszonyított sorrendjét.",
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
    legend.textContent = "Melyik program követi a megadott levezetési sorrendet?";
    options.className = "practice-options";

    shuffled(task.options).forEach((option) => {
      const label = document.createElement("label");
      const input = document.createElement("input");
      const code = document.createElement("code");

      label.className = "practice-option";
      input.type = "radio";
      input.name = `lesson7-answer-${index}`;
      input.value = option.value;
      code.textContent = option.code;
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
    document.querySelectorAll("[data-lesson7-practice]").forEach((mount, index) => {
      const task = tasks[mount.dataset.lesson7Practice];
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
