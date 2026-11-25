"""Draw one extremal pair of stars used in the thirteen-vertex argument."""

from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt


def draw() -> None:
    blue, ink = "#204b69", "#192c3a"
    fig, ax = plt.subplots(figsize=(7.0, 1.1))
    fig.subplots_adjust(left=0.01, right=0.99, bottom=0.02, top=0.98)
    ax.set(xlim=(-0.82, 13.8), ylim=(-1.22, 1.78))
    ax.axis("off")
    ax.text(-0.78, 1.40, "Edges from", fontsize=9, color=ink)
    ax.text(5.05, 1.40, "Eleven points of a monochromatic clique", ha="center",
            fontsize=9, color=ink)
    for column in range(11):
        ax.text(column + 0.15, 0.90, str(column + 1), ha="center", va="center",
                fontsize=8, color=ink)
    for label, y, misses in [("x", 0.22, {0, 2, 5, 8}), ("y", -0.69, {1, 2, 7, 10})]:
        ax.text(-0.55, y, label, va="center", fontsize=12, fontstyle="italic", color=ink)
        for column in range(11):
            ax.scatter(column + 0.15, y, s=39, linewidths=1.2, edgecolors=blue,
                       facecolors="white" if column in misses else blue)
    for y, label, face in [(0.22, "clique color", blue), (-0.69, "other color", "white")]:
        ax.scatter(11.24, y, s=39, linewidths=1.2, edgecolors=blue, facecolors=face)
        ax.text(11.66, y, label, va="center", fontsize=9, color=ink)
    directory = Path(__file__).resolve().parent
    fig.savefig(directory / "row-collision.pdf", metadata={"Author": "Robert Sneiderman"})
    fig.savefig(directory / "row-collision.png", dpi=240, facecolor="white")
    plt.close(fig)


if __name__ == "__main__":
    draw()
