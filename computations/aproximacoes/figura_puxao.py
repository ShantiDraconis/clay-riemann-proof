"""Figura: como zeros fora da reta puxariam as caudas (modelo do par isolado no fluxo de de Bruijn, t < 0), sobre os
14 380 683 zeros contíguos certificados. Em t = 0 (a própria ζ) nada está fora da reta.

    python3 figura_puxao.py pasta_c1 pasta_c2
"""
import gzip
import json
import math
import sys
from decimal import Decimal
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

SURF, INK, INK2, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#e4e3df"
CORES = ["#0d366b", "#2a78d6", "#1baf7a", "#eda100", "#eb6834"]
plt.rcParams.update({
    "figure.facecolor": SURF, "axes.facecolor": SURF, "savefig.facecolor": SURF, "axes.edgecolor": GRID,
    "axes.labelcolor": INK2, "xtick.color": INK2, "ytick.color": INK2, "text.color": INK, "axes.grid": True,
    "grid.color": GRID, "grid.linewidth": 0.6, "axes.spines.top": False, "axes.spines.right": False,
    "font.size": 9.5, "axes.titlesize": 10.5, "axes.titleweight": "bold", "axes.titlelocation": "left",
    "legend.frameon": False, "legend.fontsize": 8.5,
})
C0 = Decimal("3000175342471.5")
h = []
for pasta, faixas in ((sys.argv[1], range(4)), (sys.argv[2], range(24))):
    for I in faixas:
        for linha in gzip.open(Path(pasta) / f"zeros{I}.csv.gz", "rt"):
            if not linha.startswith("indice"):
                h.append(float(Decimal(linha.split(",")[1]) - C0))
h = np.array(h)
delta = 2 * math.pi / math.log(3.000177e12 / (2 * math.pi))
gaps = np.diff(h)
NG = len(gaps)


def depois(t):
    fora = np.nonzero(gaps ** 2 < -2 * t)[0]
    fora = fora[(fora > 0) & (fora < NG - 1)]
    rem = np.zeros(NG, bool)
    rem[fora] = rem[fora - 1] = rem[fora + 1] = True
    return np.concatenate([gaps[~rem], gaps[fora - 1] + gaps[fora] + gaps[fora + 1]]) / delta, fora


def br(v, f):
    return format(v, f).replace(".", ",")


ts = [0, -1e-6, -1e-5, -1e-4, -1e-3]
rotulo = {0: "t = 0 (ζ: nada fora da reta)", -1e-6: "t = −10⁻⁶", -1e-5: "t = −10⁻⁵", -1e-4: "t = −10⁻⁴",
          -1e-3: "t = −10⁻³"}
fig, axs = plt.subplots(2, 2, figsize=(13.5, 10.2), gridspec_kw={"hspace": 0.42, "wspace": 0.27})
xs = np.logspace(-3, 0, 60)
xl = np.linspace(1.5, 4.2, 60)
for t, cor in zip(ts, CORES):
    novo, fora = depois(t)
    ns = np.sort(novo)
    F = np.searchsorted(ns, xs) / len(ns)
    m = F > 0
    axs[0, 0].plot(xs[m], F[m], color=cor, lw=2, label=f"{rotulo[t]}: {len(fora)} pares fora")
    G = 1 - np.searchsorted(ns, xl, side="right") / len(ns)
    m = G > 0
    axs[0, 1].plot(xl[m], G[m], color=cor, lw=2, label=rotulo[t])
ax = axs[0, 0]
ax.set_xscale("log"); ax.set_yscale("log")
ax.set_xlabel("x (espaçamento normalizado na reta)")
ax.set_ylabel("fração dos espaçamentos com s < x")
ax.set_title("(a) A cauda curta é comida: os pares mais próximos saem da reta primeiro")
ax.legend(loc="lower right")
ax = axs[0, 1]
ax.set_yscale("log")
ax.set_xlabel("x (espaçamento normalizado na reta)")
ax.set_ylabel("fração dos espaçamentos com s > x")
ax.set_title("(b) A cauda longa engorda: cada par que sai deixa um vazio de ~2,8")
ax.legend(loc="lower left")

ser = json.load(open("puxao_serie.json"))["serie"]
tt = np.array([-r["t"] for r in ser])
pares = np.array([r["pares"] for r in ser])
bmax = np.array([r["b_max"] for r in ser])
ax = axs[1, 0]
m = pares > 0
ax.plot(tt[m], pares[m], color=CORES[1], lw=2, marker="o", markersize=4)
ax.set_xscale("log"); ax.set_yscale("log")
ax.set_xlabel("|t| (quanto se empurra para trás no fluxo de de Bruijn)")
ax.set_ylabel("pares fora da reta (de 14 380 682)")
ax.set_title("(c) Quantos saem: o primeiro em |t| = 1,91·10⁻⁷ (o par 808 945/946)")
for tv in (1e-6, 1e-5, 1e-4, 1e-3):
    k = int(np.argmin(abs(tt - tv)))
    ax.annotate(f"{pares[k]}", (tt[k], pares[k]), xytext=(-4, 8), textcoords="offset points", fontsize=8,
                color=INK2, ha="right")
ax = axs[1, 1]
ax.plot(tt[m], bmax[m], color=CORES[4], lw=2, marker="o", markersize=4, label="b do primeiro par a sair")
ax.plot(tt, np.sqrt(2 * tt) / 2, color=INK2, lw=1, ls="--", label="limite √(2|t|)/2 (par colado)")
ax.set_xscale("log"); ax.set_yscale("log")
ax.set_xlabel("|t|")
ax.set_ylabel("b = |Re s − ½| do par mais afastado")
ax.set_title("(d) Quão longe de ½ eles vão: b cresce como √|t|")
ax.legend(loc="upper left")
fig.suptitle("Como zeros fora da reta puxariam as caudas — modelo do par isolado sobre os 14 380 683 zeros certificados",
             x=0.06, ha="left", fontsize=12.5, fontweight="bold")
fig.text(0.06, 0.005, "Em t = 0 (a própria ζ) nenhum zero está fora da reta. O fluxo de de Bruijn para trás (t < 0) "
         "não é ζ; mostra o que aconteceria com as caudas se pares saíssem.", fontsize=8.5, color=INK2)
fig.savefig("puxao_das_caudas.png", dpi=150, bbox_inches="tight")
print("ok")
