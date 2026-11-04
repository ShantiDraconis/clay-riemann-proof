"""Figura: a refutação tendendo à prova na família Z_t = ζ L(χ₋₂₀) + t L(χ₋₄) L(χ₅).

    python3 figura_homotopia.py      (lê homotopia_seguir.json e homotopia_resumo.json; grava homotopia.png)

(a) b(t) = Re ρ(t) − ½ dos 13 pares fora da reta de Epstein (t = 1) até chegarem à reta (t = t_c).
(b) A lei da raiz quadrada: b² contra t − t_c, em log-log, com a reta b² = C(t − t_c).
(c) O defeito do círculo 1 − |1 − 1/ρ̃|² = 2b/|ρ̃|² (ρ̃ = espelho com Re < ½), a identidade da refutação, indo a 0.
"""
import json

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

SURF, INK, INK2, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#e4e3df"
plt.rcParams.update({
    "figure.facecolor": SURF, "axes.facecolor": SURF, "savefig.facecolor": SURF, "axes.edgecolor": GRID,
    "axes.labelcolor": INK2, "xtick.color": INK2, "ytick.color": INK2, "text.color": INK, "axes.grid": True,
    "grid.color": GRID, "grid.linewidth": 0.6, "axes.spines.top": False, "axes.spines.right": False,
    "font.size": 9.5, "axes.titlesize": 10.5, "axes.titleweight": "bold", "axes.titlelocation": "left",
    "legend.frameon": False, "legend.fontsize": 8,
})
seg = json.load(open("homotopia_seguir.json"))["zeros"]
res = json.load(open("homotopia_resumo.json"))["pares"]
cmap = plt.get_cmap("viridis")
fig, ax = plt.subplots(1, 3, figsize=(14, 4.6))
for k, (z, r) in enumerate(zip(seg, res)):
    cor = cmap(k / 12)
    tr = [(t, re, im) for t, re, im in z["trajetoria"]]
    ts = [p[0] for p in tr]
    bs = [abs(p[1] - 0.5) for p in tr]
    lab = f"γ ≈ {z['rho_t1'][1]:.1f}".replace(".", ",")
    ax[0].plot(ts, bs, color=cor, lw=1.6, label=lab)
    ax[0].plot([r["t_c"]], [0], "o", ms=5, color=cor, mec=SURF, mew=1)
    pts = [(t - r["t_c"], b * b) for t, b in zip(ts, bs) if t - r["t_c"] > 1e-6 and b > 0.003]
    ax[1].loglog([p[0] for p in pts], [p[1] / r["C"] for p in pts], "o", ms=3, color=cor, alpha=0.8)
    dfe = [2 * b / ((0.5 - b) ** 2 + im ** 2) for (t, re, im), b in zip(tr, bs)]
    ax[2].semilogy(ts, [max(x, 1e-9) for x in dfe], color=cor, lw=1.6)
ax[1].loglog([1e-6, 1], [1e-6, 1], color=INK, lw=1, ls="--", label="b² = C·(t − t_c)")
ax[0].set_xlim(1.02, -0.02)
ax[0].set_xlabel("t   (1 = Epstein m² + 5n²;  0 = Dedekind de Q(√−5))")
ax[0].set_ylabel("b = |Re ρ − ½|")
ax[0].set_title("(a) Os 13 pares voltam à reta")
h0, l0 = ax[0].get_legend_handles_labels()
ax[1].set_xlabel("t − t_c")
ax[1].set_ylabel("b²/C")
ax[1].set_title("(b) Lei da raiz quadrada perto de t_c")
ax[1].legend(loc="upper left")
ax[1].add_artist(ax[1].legend_)
ax[1].legend(h0, l0, ncol=2, fontsize=7, loc="lower right", title="par (altura em t = 1)", title_fontsize=7.5)
ax[2].set_xlim(1.02, -0.02)
ax[2].set_ylim(1e-7, 1e-2)
ax[2].set_xlabel("t")
ax[2].set_ylabel("1 − |1 − 1/ρ̃|² = 2b/|ρ̃|²")
ax[2].set_title("(c) A identidade da refutação → 0")
fig.tight_layout()
fig.savefig("homotopia.png", dpi=150)
print("ok")
