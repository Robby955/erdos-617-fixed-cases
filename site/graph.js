const canvas = document.getElementById("graph");
const context = canvas.getContext("2d");
const caption = document.getElementById("caption");
const controls = document.querySelectorAll("[data-mode]");

const width = 480;
const height = 294;
const palette = ["#be572d", "#137d6a", "#2956ad"];
const witness = new Set([0, 4, 8, 9]);
const captions = {
  grid: "Every four of these nine vertices span all three colors.",
  ten: "Join J to the nine original points in blue. Can you find four vertices joined only by blue edges?",
  witness: "A, E, I and J span six blue edges. Both green and orange are missing."
};

function edgeColor(i, j) {
  if (j === 9) return 2;
  if (i % 3 === j % 3) return 0;
  if (Math.floor(i / 3) === Math.floor(j / 3)) return 1;
  return 2;
}

function draw(mode) {
  const gridOnly = mode === "grid";
  const highlight = mode === "witness";
  const points = Array.from({length: 9}, (_, i) => [
    (gridOnly ? 127 : 55) + (i % 3) * 113,
    41 + Math.floor(i / 3) * 106
  ]);
  if (!gridOnly) points.push([418, 150]);

  const ratio = Math.max(1, window.devicePixelRatio || 1);
  canvas.width = Math.round(width * ratio);
  canvas.height = Math.round(height * ratio);
  context.setTransform(ratio, 0, 0, ratio, 0, 0);
  // Draw the six witness edges last so the rest of the graph cannot obscure them.
  for (const foreground of highlight ? [false, true] : [false]) {
    for (let i = 0; i < points.length; i++) {
      for (let j = i + 1; j < points.length; j++) {
        const chosen = highlight && witness.has(i) && witness.has(j);
        if (chosen !== foreground) continue;
        const [x, y] = points[i];
        const [u, v] = points[j];
        const color = edgeColor(i, j);
        context.strokeStyle = palette[color];
        context.globalAlpha = highlight ? (chosen ? 1 : 0.12) : 0.77;
        context.lineWidth = chosen ? 3.3 : 1.6;
        context.beginPath();
        context.moveTo(x, y);
        // A long edge must remain visible when it passes a third vertex.
        const bend = Math.hypot(u - x, v - y) > 188 ? 0.09 : 0;
        context.quadraticCurveTo((x + u) / 2 - bend * (v - y),
                                 (y + v) / 2 + bend * (u - x), u, v);
        context.stroke();
      }
    }
  }
  points.forEach(([x, y], i) => {
    const chosen = highlight && witness.has(i);
    context.globalAlpha = highlight && !chosen ? 0.44 : 1;
    context.beginPath();
    context.arc(x, y, chosen ? 6.7 : 5.5, 0, 2 * Math.PI);
    context.fillStyle = chosen ? palette[2] : "#172328";
    context.fill();
    context.strokeStyle = "#fff";
    context.lineWidth = 1.6;
    context.stroke();
    const letter = String.fromCharCode(65 + i);
    context.font = '550 15px "Instrument Sans", Arial, sans-serif';
    context.lineWidth = 4;
    context.strokeText(letter, x + 8, y - 9);
    context.fillText(letter, x + 8, y - 9);
  });
  context.globalAlpha = 1;
  caption.textContent = captions[mode];
  canvas.setAttribute("aria-label", captions[mode]);
  for (const button of controls) {
    button.setAttribute("aria-pressed", String(button.dataset.mode === mode));
  }
}

for (const button of controls) {
  button.addEventListener("click", () => draw(button.dataset.mode));
}
draw("grid");
document.fonts.ready.then(() => draw(document.querySelector('[data-mode][aria-pressed="true"]').dataset.mode));
