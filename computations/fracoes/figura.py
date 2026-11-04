"""Figura: as caudas em frações e as frações de quebra dos outros problemas.

    python3 figura.py      (lê caudas_gama.json, sat3_n*.json, sato_tate.json; grava fracoes.png)

(a) A cauda {γ} dos 14 380 683 zeros em 100 caixas: desvio relativo da contagem esperada (equidistribuição, Hlawka).
(b) Os quocientes parciais certificados da fração contínua das caudas contra Gauss–Kuzmin.
(c) P vs NP: fração de fórmulas 3-SAT satisfatíveis contra α = cláusulas/variáveis, para n = 25, 50, 100.
(d) BSD: x_p = a_p/(2√p) para E₂: y² = x³ + x + 1 (sem CM) contra Sato–Tate (2/π)√(1 − x²).
"""
import json
import math
import os

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

SURF, INK, INK2, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#e4e3df"
CORES = ["#0d366b", "#2a78d6", "#1baf7a", "#eda100", "#eb6834"]
plt.rcParams.update({
    "figure.facecolor": SURF, "axes.facecolor": SURF, "savefig.facecolor": SURF, "axes.edgecolor": GRID,
    "axes.labelcolor": INK2, "xtick.color": INK2, "ytick.color": INK2, "text.color": INK, "axes.grid": True,
    "grid.color": GRID, "grid.linewidth": 0.6, "axes.spines.top": False, "axes.spines.right": False,
    "font.size": 9.5, "axes.titlesize": 10.5, "axes.titleweight": "bold", "axes.titlelocation": "left",
    "legend.frameon": False, "legend.fontsize": 8.5,
})
G = json.load(open("caudas_gama.json"))
fig, ax = plt.subplots(2, 2, figsize=(12, 8.2))
a = ax[0, 0]
cont = G["equidistribuicao"]["contagens"]
esp = G["zeros"] / 100
sig = 100 / math.sqrt(esp)
a.axhspan(-2 * sig, 2 * sig, color=GRID, alpha=0.7, lw=0, label="±2σ de Poisson", zorder=0)
a.bar([(k + 0.5) / 100 for k in range(100)], [(c - esp) / esp * 100 for c in cont], width=0.008, color=CORES[1],
      zorder=2)
a.axhline(0, color=INK2, lw=0.8)
eq = G["equidistribuicao"]
a.set_title("(a) A cauda {γ} é uniforme: χ² = " + f"{eq['qui2']:.0f}" + " (99 g.l.), KS·√N = "
            + f"{eq['ks_vezes_raiz_N']:.2f}".replace(".", ","))
a.set_xlabel("cauda {γ} (parte depois da vírgula)")
a.set_ylabel("desvio da contagem esperada (%)")
a.legend(loc="lower right")
b = ax[0, 1]
gk = G["fracao_continua"]["gauss_kuzmin"]
ks = [g["k"] for g in gk]
b.semilogy(ks, [g["gauss_kuzmin"] for g in gk], color=INK, lw=1.2, ls="--", label="Gauss–Kuzmin log₂(1 + 1/(k(k+2)))")
b.semilogy(ks, [g["observado"] for g in gk], "o", ms=6, color=CORES[0], mec=SURF, mew=1.2,
           label="quocientes certificados pela bola (10⁶ zeros)")
b.set_xlabel("quociente parcial k")
b.set_ylabel("frequência")
b.set_title("(b) As frações contínuas das caudas seguem Gauss–Kuzmin")
b.legend(loc="upper right")
c = ax[1, 0]
for n, cor in ((25, CORES[3]), (50, CORES[1]), (100, CORES[0])):
    f = f"sat3_n{n}.json"
    if os.path.exists(f) and os.path.getsize(f) > 0:
        d = json.load(open(f))
        c.plot([p["alfa"] for p in d["pontos"]], [p["fracao_satisfativel"] for p in d["pontos"]], "o-", ms=4,
               color=cor, lw=1.8, label=f"n = {n}")
c.axvline(4.267, color=CORES[4], lw=1.4, ls="--")
c.text(4.3, 0.92, "α ≈ 4,267 (previsão)", color=INK, fontsize=8.5)
c.axvline(5.19, color=INK2, lw=1, ls=":")
c.text(5.22, 0.6, "1º momento:\nα ≤ 5,19 (kernel)", color=INK2, fontsize=8)
c.set_xlabel("α = cláusulas / variáveis")
c.set_ylabel("fração satisfatível")
c.set_title("(c) P vs NP no cotidiano: a quebra do 3-SAT aleatório")
c.legend(loc="lower left")
d_ = ax[1, 1]
if os.path.exists("sato_tate.json") and os.path.getsize("sato_tate.json") > 0:
    S = json.load(open("sato_tate.json"))["curvas"]
    e2 = S["E2: y² = x³ + x + 1"]
    bordas = e2["bordas"]
    w = bordas[1] - bordas[0]
    tot = sum(e2["histograma"])
    d_.bar([(bordas[k] + bordas[k + 1]) / 2 for k in range(len(bordas) - 1)], [h / (tot * w) for h in e2["histograma"]],
           width=w * 0.85, color=CORES[2], label=f"E₂: y² = x³ + x + 1 ({e2['primos']} primos)")
    xs = [-1 + k / 200 for k in range(401)]
    d_.plot(xs, [2 / math.pi * math.sqrt(max(0.0, 1 - x * x)) for x in xs], color=INK, lw=1.4, ls="--",
            label="Sato–Tate (2/π)√(1 − x²)")
    d_.set_xlim(-1.05, 1.05)
    d_.set_ylim(0, 0.9)
    d_.legend(loc="upper center", fontsize=8, ncol=1)
d_.set_xlabel("x_p = a_p / (2√p)   (Hasse: |x_p| ≤ 1)")
d_.set_ylabel("densidade")
d_.set_title("(d) BSD: a fração a_p/(2√p) segue Sato–Tate")
fig.tight_layout()
fig.savefig("fracoes.png", dpi=150)
print("ok")
