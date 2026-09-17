window.addEventListener('message', event => {
  if (event.origin !== window.location.origin) return;
  if (event.data?.type !== 'matlog-rocq-resize') return;

  const frame = [...document.querySelectorAll('iframe.rocq-frame--example')]
    .find(candidate => candidate.contentWindow === event.source);

  if (!frame) return;

  const requestedHeight = Number(event.data.height);
  const safeHeight = Math.max(160, Math.min(950, requestedHeight || 680));
  frame.style.height = `${safeHeight}px`;
});
