"""Figura: φ, Fibonacci e os quartetos.

    python3 figura.py      (lê aurea.json; grava aurea.png)

(a) Os quartetos fora da reta que existem (Epstein m² + 5n², Davenport–Heilbronn): quanto o ângulo da diagonal fica
    abaixo de meia volta de π (½ − θ/π) contra b/(πγ).
(b) O teste "seguem φ?": parte fracionária de log_φ(γ/b) de cada quarteto; com estrutura φ ela se acumularia em 0 ou 1.
(c) A "zeta de Fibonacci" com produto de Euler (L(s, χ₅), o fator novo de ζ_{ℚ(√5)}) tem os zeros na reta; a sem
    produto de Euler (Σ F_n^{−s}) tem zeros espalhados e polos em Re s = 0 e −2, espaçados 2π/log φ.
(d) As frações F_{n+1}/F_n: F_n²·|φ − F_{n+1}/F_n| → 1/√5 = |5^{−s}| na reta = lim F_n/φⁿ.
"""
import json
import math

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

SURF, INK, INK2, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#e4e3df"
AZUL, LARANJA, VIOLETA, AQUA = "#2a78d6", "#eb6834", "#6250d6", "#1baf7a"
plt.rcParams.update({
    "figure.facecolor": SURF, "axes.facecolor": SURF, "savefig.facecolor": SURF, "axes.edgecolor": GRID,
    "axes.labelcolor": INK2, "xtick.color": INK2, "ytick.color": INK2, "text.color": INK, "axes.grid": True,
    "grid.color": GRID, "grid.linewidth": 0.6, "axes.spines.top": False, "axes.spines.right": False,
    "font.size": 9.5, "axes.titlesize": 10.5, "axes.titleweight": "bold", "axes.titlelocation": "left",
    "legend.frameon": False, "legend.fontsize": 8.5,
})
D = json.load(open("aurea.json"))
Q = D["quartetos"]
fig, ax = plt.subplots(2, 2, figsize=(12.5, 9.2))

a = ax[0, 0]
for nome, cor, rot in (("Epstein m²+5n²", VIOLETA, "Epstein m² + 5n² (12)"), ("Davenport–Heilbronn", AQUA,
                                                                                  "Davenport–Heilbronn (3)")):
    qs = Q[nome]["quartetos"]
    x = [q["b"] / (math.pi * q["gama"]) for q in qs]
    y = [q["falta_para_meio"] for q in qs]
    a.loglog(x, y, "o", ms=8, color=cor, mec=SURF, mew=1.5, label=rot, zorder=3)
xx = np.logspace(-4.5, -1.8, 50)
a.loglog(xx, xx, color=INK2, lw=1, ls="--", label="½ − θ/π = b/(πγ)")
a.set_xlabel("b/(πγ)")
a.set_ylabel("½ − θ/π   (θ = ângulo da diagonal do quarteto)")
a.set_title("(a) O ângulo do quarteto tende a meia volta de π")
a.legend(loc="upper left")

b = ax[0, 1]
for k, (nome, cor) in enumerate((("Epstein m²+5n²", VIOLETA), ("Davenport–Heilbronn", AQUA))):
    fr = [q["frac_logphi_razao"] for q in Q[nome]["quartetos"]]
    b.plot(fr, [k] * len(fr), "o", ms=9, color=cor, mec=SURF, mew=1.5, zorder=3)
b.axvspan(0, 0.1, color=GRID, lw=0, zorder=0)
b.axvspan(0.9, 1, color=GRID, lw=0, zorder=0)
b.text(0.005, 1.38, "aqui, se γ/b fosse\nperto de uma potência de φ", fontsize=8, color=INK2, va="top")
t = Q["teste_phi"]
b.text(0.33, -0.55, f"KS = {t['ks_frac_logphi_razao']:.2f} (crítico a 5%: {t['ks_critico_5pc']:.2f}): "
       "compatível com uniforme".replace(".", ","), fontsize=8.5, color=INK)
b.set_yticks([0, 1], ["Epstein", "Davenport–\nHeilbronn"])
b.set_ylim(-0.8, 1.5)
b.set_xlim(0, 1)
b.set_xlabel("parte fracionária de log_φ(γ/b)")
b.set_title("(b) Os zeros fora da reta não seguem φ")
b.grid(axis="y", visible=False)

c = ax[1, 0]
zl = D["zeros_L_chi5"]["zeros_na_reta"]
c.plot([0.5] * len(zl), zl, "o", ms=6, color=AZUL, mec=SURF, mew=1.2, zorder=3,
       label=f"L(s, χ₅): {len(zl)} zeros\naté 40, todos na reta")
zf = D["zeta_fibonacci"]
zx = [r["s"][0] for r in zf["zeros"]]
zy = [r["s"][1] for r in zf["zeros"]]
c.plot(zx, zy, "o", ms=7, color=LARANJA, mec=SURF, mew=1.2, zorder=3, label=f"Σ F_n^−s: {len(zx)} zeros\naté 45, espalhados")
lp = math.log((1 + 5 ** 0.5) / 2)
px = [0.0] * 4 + [-2.0] * 4
py = [2 * math.pi * m / lp for m in range(4)] + [(2 * m + 1) * math.pi / lp for m in range(4)]
c.plot(px, py, "x", ms=8, mew=1.8, color=INK2, zorder=2, label="polos de Σ F_n^−s\n(passo 2π/log φ ≈ 13,06)")
c.axvline(0.5, color=AZUL, lw=0.8, ls=":")
c.set_xlim(-3.6, 4.6)
c.set_ylim(0, 46)
c.set_xlabel("Re s")
c.set_ylabel("Im s")
c.set_title("(c) Com produto de Euler, a reta; sem ele, nenhuma linha")
c.legend(loc="center right", fontsize=8, frameon=True, facecolor=SURF, edgecolor=GRID)

d = ax[1, 1]
H = D["hurwitz"]["tabela"][:24]
n = [r["n"] for r in H]
v = [r["Fn2_vezes_erro"] for r in H]
d.plot(n, v, "o-", ms=5, color=AZUL, lw=1.6, mec=SURF, mew=1.2, zorder=3, label="F_n²·|φ − F_{n+1}/F_n|")
d.axhline(1 / math.sqrt(5), color=LARANJA, lw=1.6, ls="--", zorder=2)
d.text(12, 1 / math.sqrt(5) + 0.03, "1/√5 = |5^−s| na reta = lim F_n/φⁿ", fontsize=8.5, color=INK)
for r in H[:5]:
    d.annotate(r["convergente"], (r["n"], r["Fn2_vezes_erro"]), xytext=(6, 4), textcoords="offset points", fontsize=8)
d.set_ylim(0.3, 0.75)
d.set_xlabel("n")
d.set_ylabel("F_n²·|φ − F_{n+1}/F_n|")
d.set_title("(d) As frações de Fibonacci e a constante 1/√5")
d.legend(loc="upper right")
fig.tight_layout()
fig.savefig("aurea.png", dpi=150)
print("ok")
