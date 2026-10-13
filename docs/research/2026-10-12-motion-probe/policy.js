// What each thing of each picture computes.
// A page under the policy default-src 'self' runs this file, which is of its own origin, and
// runs no script that is inline.
function report() {
  const table = document.getElementById('computed');
  if (!table) return;
  let rows = '<tr><th>picture</th><th>thing</th><th>has a style attribute</th>' +
    '<th>animation-name</th><th>animation-duration</th><th>play state</th>' +
    '<th>animations</th></tr>';
  for (const svg of document.querySelectorAll('svg[id]')) {
    for (const el of svg.querySelectorAll('[data-key]')) {
      const cs = getComputedStyle(el);
      rows += '<tr><td>' + svg.id + '</td><td>' + el.dataset.key + '</td><td>' +
        (el.hasAttribute('style') ? 'yes' : 'no') + '</td><td>' +
        cs.getPropertyValue('animation-name') + '</td><td>' +
        cs.getPropertyValue('animation-duration') + '</td><td>' +
        cs.getPropertyValue('animation-play-state') + '</td><td>' +
        el.getAnimations().length + '</td></tr>';
    }
  }
  table.innerHTML = rows;
  const scrubbed = document.getElementById('scrubbed');
  const says = document.getElementById('says');
  if (scrubbed && says) {
    says.textContent = getComputedStyle(scrubbed).getPropertyValue('--t').trim();
  }
}
window.addEventListener('load', () => {
  requestAnimationFrame(() => requestAnimationFrame(report));
  const slider = document.getElementById('slider');
  const scrubbed = document.getElementById('scrubbed');
  if (slider && scrubbed) slider.addEventListener('input', () => {
    scrubbed.style.setProperty('--t', slider.value);
    report();
  });
});
