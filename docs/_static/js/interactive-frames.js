window.addEventListener('message', event => {
  if (event.origin !== window.location.origin) return;
  if (event.data?.type !== 'matlog-rocq-resize') return;

  const frame = [...document.querySelectorAll('iframe.rocq-frame--example, iframe.practice-frame')]
    .find(candidate => candidate.contentWindow === event.source);

  if (!frame) return;

  const requestedHeight = Number(event.data.height);
  const maximumHeight = frame.classList.contains('practice-frame') ? 12000 : 950;
  const safeHeight = Math.max(160, Math.min(maximumHeight, requestedHeight || 680));
  frame.style.height = `${safeHeight}px`;
});
