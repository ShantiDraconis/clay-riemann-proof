"""Figura: os 112 zeros da zeta de Fibonacci até a altura 300 e como eles se ligam.

    python3 figura_zeros_fibonacci.py      (lê zeros_fibonacci.json; grava zeros_fibonacci.png)

(a) O plano (altura t na horizontal, Re s na vertical): polos em Re s = 0, −2, −4 (passo P = 2π/log φ); cada polo de
    Re s = 0 com o seu zero companheiro (segmento); as cadeias de zeros que entram pela esquerda e andam um passo por
    período (linha); os demais zeros (faixa); a reta ½ de ζ e a cota σ* à direita da qual não há zero.
(b) Tudo dobrado módulo P: cada família fica numa fase.
(c) A parte real do companheiro do polo m: o padrão se repete a cada 3 períodos, porque log √5/log φ ≈ 5/3.
"""
import json
import math

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

SURF, INK, INK2, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#e4e3df"
AZUL, LARANJA, AQUA, CINZA = "#2a78d6", "#eb6834", "#1baf7a", "#a3a29c"
plt.rcParams.update({
    "figure.facecolor": SURF, "axes.facecolor": SURF, "savefig.facecolor": SURF, "axes.edgecolor": GRID,
    "axes.labelcolor": INK2, "xtick.color": INK2, "ytick.color": INK2, "text.color": INK, "axes.grid": True,
    "grid.color": GRID, "grid.linewidth": 0.6, "axes.spines.top": False, "axes.spines.right": False,
    "font.size": 9.5, "axes.titlesize": 10.5, "axes.titleweight": "bold", "axes.titlelocation": "left",
    "legend.frameon": False, "legend.fontsize": 8.5,
})
D = json.load(open("zeros_fibonacci.json"))
P = D["periodo_P"]
Z = [complex(a, b) for a, b in D["zeros"]]
POL = [complex(a, b) for a, b in D["polos"]]
comp = D["companheiros"]
cad = [c for c in D["cadeias"] if len(c) > 2]
ids_comp = {(round(c["zero"][0], 6), round(c["zero"][1], 6)) for c in comp}
ids_cad = {(round(a, 6), round(b, 6)) for c in cad for a, b in c}
resto = [z for z in Z if (round(z.real, 6), round(z.imag, 6)) not in ids_comp | ids_cad]

fig = plt.figure(figsize=(13, 9.6))
gs = fig.add_gridspec(2, 2, height_ratios=[1.15, 1])
a = fig.add_subplot(gs[0, :])
a.axhline(0.5, color=AZUL, lw=0.9, ls=":", zorder=1)
a.text(301, 0.5, "Re s = ½", fontsize=8, color=AZUL, va="center")
a.axhline(D["sigma_estrela_sem_zeros_a_direita"], color=INK2, lw=1, ls="--", zorder=1)
a.text(301, D["sigma_estrela_sem_zeros_a_direita"] + 0.05, f"σ* = {D['sigma_estrela_sem_zeros_a_direita']:.3f}".replace(".", ","),
       fontsize=8, color=INK2, va="bottom")
a.plot([z.imag for z in resto], [z.real for z in resto], "o", ms=4, color=CINZA, zorder=2, label="demais zeros (faixa)")
for c in comp:
    a.plot([c["polo_t"], c["zero"][1]], [0, c["zero"][0]], color=AZUL, lw=1.2, zorder=2)
a.plot([c["zero"][1] for c in comp], [c["zero"][0] for c in comp], "o", ms=6, color=AZUL, mec=SURF, mew=1, zorder=3,
       label="companheiro de cada polo de Re s = 0")
for k, c in enumerate(cad):
    a.plot([y for x, y in c], [x for x, y in c], "o-", ms=6, lw=1.6, color=LARANJA, mec=SURF, mew=1, zorder=3,
           label="cadeias: um passo por período" if k == 0 else None)
a.plot([p.imag for p in POL], [p.real for p in POL], "x", ms=6, mew=1.6, color=INK, zorder=4,
       label="polos (passo P = 2π/log φ ≈ 13,06)")
a.set_xlim(0, 300)
a.set_ylim(-4.7, 1.05)
a.set_xlabel("altura t = Im s")
a.set_ylabel("Re s")
a.set_title(f"(a) Os {D['n_zeros']} zeros de Σ F_n^−s até t = 300 (contagem conferida pelo princípio do argumento) "
            "e como se ligam")
a.legend(loc="lower right", ncol=2, fontsize=8, frameon=True, facecolor=SURF, edgecolor=GRID)

b = fig.add_subplot(gs[1, 0])
fz = lambda z: (z.imag % P) / P
b.plot([fz(z) for z in resto], [z.real for z in resto], "o", ms=4, color=CINZA, zorder=2)
b.plot([fz(complex(*c["zero"])) for c in comp], [c["zero"][0] for c in comp], "o", ms=6, color=AZUL, mec=SURF, mew=1,
       zorder=3)
for c in cad:
    b.plot([fz(complex(x, y)) for x, y in c], [x for x, y in c], "o", ms=6, color=LARANJA, mec=SURF, mew=1, zorder=3)
for p in POL:
    b.plot(fz(p), p.real, "x", ms=8, mew=1.8, color=INK, zorder=4)
    if fz(p) < 0.02:
        b.plot(1.0, p.real, "x", ms=8, mew=1.8, color=INK, zorder=4)
b.axhline(0.5, color=AZUL, lw=0.9, ls=":")
b.set_xlim(-0.02, 1.02)
b.set_ylim(-4.7, 1.05)
b.set_xlabel("fase (t mod P)/P")
b.set_ylabel("Re s")
b.set_title("(b) Dobrado módulo P: cada família tem a sua fase")

c = fig.add_subplot(gs[1, 1])
cores = {0: AZUL, 1: LARANJA, 2: AQUA}
for r in (0, 1, 2):
    sel = [x for x in comp if x["m_mod_3"] == r]
    c.plot([x["m"] for x in sel], [x["zero"][0] for x in sel], "o-", ms=6, lw=1.4, color=cores[r], mec=SURF, mew=1,
           label=f"m ≡ {r} (mod 3)")
c.axhline(0.5, color=AZUL, lw=0.9, ls=":")
c.set_xlabel("m (polo em t = mP)")
c.set_ylabel("Re do zero companheiro")
c.set_title("(c) O padrão repete a cada 3 períodos: log √5/log φ ≈ 5/3")
c.text(1, -0.12, f"giro por período = {D['giro_fracao']:.4f} volta ≈ 2/3;  φ⁵ = {D['phi5']:.3f} ≈ √5³ = {D['raiz5_cubo']:.3f}"
       .replace(".", ","), fontsize=8.5, color=INK2)
c.set_ylim(-0.2, 0.75)
c.legend(loc="upper right", ncol=3, fontsize=8)
fig.tight_layout()
fig.savefig("zeros_fibonacci.png", dpi=150)
print("ok")
