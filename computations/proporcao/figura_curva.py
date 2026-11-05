"""Figura: quanto o método de 2026 dá para cada alcance A da correlação de pares.

    python3 figura_curva.py      (lê curva.json; grava curva.png)

(a) A fração dos zeros garantida pelo método em função de A: simples e na reta, distintos, simples ou na reta; e a
    cota fechada 1 − 1/(3A²) da densidade uniforme. A = 1 é o que se sabe hoje (67,25%).
(b) As densidades ótimas g = η² (o "peso" do método) para A = 1, 1,5, 2 e 3.
"""
import json

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

from curva import otimo

SURF, INK, INK2, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#e4e3df"
AZUL, LARANJA, VIOLETA, AQUA = "#2a78d6", "#eb6834", "#6250d6", "#1baf7a"
plt.rcParams.update({
    "figure.facecolor": SURF, "axes.facecolor": SURF, "savefig.facecolor": SURF, "axes.edgecolor": GRID,
    "axes.labelcolor": INK2, "xtick.color": INK2, "ytick.color": INK2, "text.color": INK, "axes.grid": True,
    "grid.color": GRID, "grid.linewidth": 0.6, "axes.spines.top": False, "axes.spines.right": False,
    "font.size": 9.5, "axes.titlesize": 10.5, "axes.titleweight": "bold", "axes.titlelocation": "left",
    "legend.frameon": False, "legend.fontsize": 8.5,
})
D = json.load(open("curva.json"))
fig, ax = plt.subplots(1, 2, figsize=(13, 5.2), gridspec_kw={"width_ratios": [1.35, 1]})

a = ax[0]
As = np.linspace(1, 6, 60)
ms = np.array([otimo(A, max(300, int(250 * A)))[0] for A in As])
a.plot(As, 100 * (1 - ms), color=AZUL, lw=2, label="simples e na reta (o número de 2026)")
a.plot(As, 100 * (1 - ms / 2), color=VIOLETA, lw=1.6, label="distintos")
a.plot(As, 100 * (1 - 2 * ms / (3 + 2 * np.sqrt(2))), color=AQUA, lw=1.6, label="simples ou na reta")
a.plot(As, 100 * (1 - 1 / (3 * As ** 2)), color=INK2, lw=1.2, ls="--", label="cota fechada 1 − 1/(3A²) (g uniforme)")
a.plot([1], [100 * D["C0_hoje"]], "o", ms=9, color=LARANJA, mec=SURF, mew=1.5, zorder=5)
a.annotate("hoje: A = 1, 67,25%\n(o máximo do método)", (1, 100 * D["C0_hoje"]), xytext=(14, -26),
           textcoords="offset points", fontsize=8.5, color=INK)
for alvo, txt in (("0.900", "90%"), ("0.950", "95%"), ("0.990", "99%")):
    A = D["alcance_necessario"][alvo]
    y = 100 * float(alvo)
    a.plot([A, A], [60, y], color=GRID, lw=1, zorder=1)
    a.plot([A], [y], "o", ms=6, color=AZUL, mec=SURF, mew=1.2, zorder=5)
    a.annotate(f"{txt} com A = {A:.2f}".replace(".", ","), (A, y), xytext=(6, -14), textcoords="offset points",
               fontsize=8)
a.axhline(100, color=INK2, lw=0.8, ls=":")
a.set_xlim(0.9, 6)
a.set_ylim(60, 101)
a.set_xlabel("alcance A até onde a correlação de pares de Montgomery é conhecida (hoje: 1)")
a.set_ylabel("fração dos zeros garantida (%)")
a.set_title("(a) O que o método de 2026 dá para cada alcance A")
a.legend(loc="lower right", fontsize=8, frameon=True, facecolor=SURF, edgecolor=GRID)

b = ax[1]
for A, cor in ((1.0, LARANJA), (1.5, AZUL), (2.0, VIOLETA), (3.0, AQUA)):
    n = 400
    m, c = otimo(A, n)
    h = A / n
    x = -A / 2 + h * (np.arange(n) + 0.5)
    b.plot(x, c / h, color=cor, lw=1.8, label=f"A = {A:g}: garante {100 * (1 - m):.2f}%".replace(".", ","))
b.set_xlabel("u")
b.set_ylabel("g(u) = η(u)²")
b.set_title("(b) As densidades ótimas (suporte [−A/2, A/2])")
b.legend(loc="upper right", fontsize=8)
fig.tight_layout()
fig.savefig("curva.png", dpi=150)
print("ok")
