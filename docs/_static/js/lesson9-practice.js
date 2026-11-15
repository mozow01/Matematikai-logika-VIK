document.addEventListener('DOMContentLoaded', () => {
  document.querySelectorAll('[data-lesson9-practice]').forEach(practice => {
    const button = practice.querySelector('[data-check]');
    const feedback = practice.querySelector('[data-feedback]');

    button?.addEventListener('click', () => {
      const questions = [...practice.querySelectorAll('fieldset[data-answer]')];
      const missing = questions.some(question => !question.querySelector('input:checked'));

      feedback.classList.remove('is-success', 'is-error');

      if (missing) {
        feedback.textContent = 'Minden sorban válasszon egy állítást.';
        feedback.classList.add('is-error');
        return;
      }

      let correct = 0;
      questions.forEach(question => {
        if (question.querySelector('input:checked')?.value === question.dataset.answer) {
          correct += 1;
        }
      });

      if (correct === questions.length) {
        feedback.textContent = 'Mind a négy átalakítás helyes.';
        feedback.classList.add('is-success');
      } else {
        feedback.textContent = `${correct} / ${questions.length} helyes. Figyeljen arra, hogy az implikáció melyik oldalán áll a kvantor.`;
        feedback.classList.add('is-error');
      }
    });
  });
});
