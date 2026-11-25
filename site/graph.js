const canvas = document.getElementById("graph");
const ctx = canvas.getContext("2d");
const caption = document.getElementById("caption");
const buttons = [...document.querySelectorAll("[data-mode]")];
const points = Array.from({length: 9}, (_, i) => [92 + (i % 3) * 120, 70 + Math.floor(i / 3) * 130]);
points.push([475, 240]);
const tones = ["#a34b32", "#235a4c", "#6268a0"];
const witness = new Set([0, 4, 8, 9]);
const descriptions = {
  grid: "In this three-color example, every four of the nine grid points see all three colors.",
  ten: "The tenth vertex joins all nine grid points by violet edges. This gives one explicit coloring of the complete graph on ten vertices.",
  witness: "The four highlighted vertices span six violet edges. Both green and rust are missing."
};

function edgeColor(i, j) {
  if (j === 9) return 2;
  if (i % 3 === j % 3) return 0;
  if (Math.floor(i / 3) === Math.floor(j / 3)) return 1;
  return 2;
}

function draw(mode) {
  const n = mode === "grid" ? 9 : 10;
  const ratio = Math.max(1, window.devicePixelRatio || 1);
  canvas.width = Math.round(560 * ratio);
  canvas.height = Math.round(420 * ratio);
  ctx.setTransform(ratio, 0, 0, ratio, 0, 0);
  const selected = mode === "witness";
  for (let pass = 0; pass < (selected ? 2 : 1); pass++) {
    for (let i = 0; i < n; i++) {
      for (let j = i + 1; j < n; j++) {
        const chosen = selected && witness.has(i) && witness.has(j);
        if (selected && Number(chosen) !== pass) continue;
        const [x, y] = points[i];
        const [u, v] = points[j];
        ctx.strokeStyle = tones[edgeColor(i, j)];
        ctx.globalAlpha = selected ? (chosen ? 0.95 : 0.09) : (j === 9 ? 0.74 : 0.53);
        ctx.lineWidth = chosen ? 3 : 1.5;
        ctx.beginPath();
        ctx.moveTo(x, y);
        // Bow long edges slightly so a third grid point never hides the connection.
        const bend = Math.hypot(u - x, v - y) > 205 ? 0.065 : 0;
        ctx.quadraticCurveTo((x + u) / 2 - bend * (v - y), (y + v) / 2 + bend * (u - x), u, v);
        ctx.stroke();
      }
    }
  }
  for (let i = 0; i < n; i++) {
    const [x, y] = points[i];
    const chosen = selected && witness.has(i);
    ctx.globalAlpha = selected && !chosen ? 0.35 : 1;
    ctx.beginPath();
    ctx.arc(x, y, chosen || i === 9 ? 9 : 6, 0, Math.PI * 2);
    ctx.fillStyle = chosen ? tones[2] : "#242821";
    ctx.fill();
    ctx.lineWidth = 2;
    ctx.strokeStyle = "#f6f4e9";
    ctx.stroke();
  }
  ctx.globalAlpha = 1;
  caption.textContent = descriptions[mode];
  canvas.setAttribute("aria-label", descriptions[mode]);
  buttons.forEach(button => button.setAttribute("aria-pressed", String(button.dataset.mode === mode)));
}
buttons.forEach(button => button.addEventListener("click", () => draw(button.dataset.mode)));
draw("grid");
