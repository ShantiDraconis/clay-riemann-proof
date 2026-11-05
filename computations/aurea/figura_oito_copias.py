"""Figura: oito cópias da estrutura de Riemann giradas de 45° em torno do 0 absoluto.

    python3 figura_oito_copias.py      (lê oito_copias.json e aurea.json; grava oito_copias.png)

(a) A estrela: os zeros de ζ até a altura 100 (cópia 0) e as suas 7 cópias giradas; as 8 retas críticas copiadas.
(b) Perto do 0: as 8 retas cercam um octógono regular de apótema ½; todo cruzamento fica em |s| ≤ 1,31, e o zero mais
    perto do 0 está em |s| = 14,13.
(c) Um braço visto de dentro: as duas retas críticas que o ladeiam (cópias k e k + 4) formam um corredor de largura 1;
    um quarteto fora da reta aparece nele como 4 pontos ±½ ± b.
(d) Em torno de ½ (comparação): as lacunas entre os pontos da órbita do quarteto; polígono regular só onde as curvas se
    cruzam, e ζ (kernel: γ/b > 26) fica longe disso.
"""
import json
import math

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

SURF, INK, INK2, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#e4e3df"
AZUL, LARANJA, VIOLETA, AQUA, CINZA = "#2a78d6", "#eb6834", "#6250d6", "#1baf7a", "#a3a29c"
plt.rcParams.update({
    "figure.facecolor": SURF, "axes.facecolor": SURF, "savefig.facecolor": SURF, "axes.edgecolor": GRID,
    "axes.labelcolor": INK2, "xtick.color": INK2, "ytick.color": INK2, "text.color": INK, "axes.grid": True,
    "grid.color": GRID, "grid.linewidth": 0.6, "axes.spines.top": False, "axes.spines.right": False,
    "font.size": 9.5, "axes.titlesize": 10.5, "axes.titleweight": "bold", "axes.titlelocation": "left",
    "legend.frameon": False, "legend.fontsize": 8.5,
})
D = json.load(open("oito_copias.json"))
EX = D["exemplos_fora_da_reta"]
W = complex(math.cos(math.pi / 4), math.sin(math.pi / 4))
zs = [complex(a, b) for a, b in D["zeros_zeta_ate_100"]]
zs = zs + [z.conjugate() for z in zs]


def reta(k, r=200.0):
    """A reta crítica da cópia k: ωᵏ(½ + iy)."""
    y = np.array([-r, r])
    return W ** k * (0.5 + 1j * y)


fig, ax = plt.subplots(2, 2, figsize=(12.5, 12))

a = ax[0, 0]
for k in range(8):
    p = reta(k)
    a.plot(p.real, p.imag, color=GRID, lw=0.9, zorder=1)
for k in range(1, 8):
    p = np.array([W ** k * z for z in zs])
    a.plot(p.real, p.imag, "o", ms=3.2, color=CINZA, zorder=2, label="as 7 cópias giradas (nenhum ponto é zero de ζ)"
           if k == 1 else None)
a.plot([z.real for z in zs], [z.imag for z in zs], "o", ms=3.6, color=AZUL, zorder=3, label="cópia 0 = ζ (29 + 29 zeros)")
for k in range(8):
    ang = math.pi / 2 + k * math.pi / 4
    a.text(112 * math.cos(ang), 112 * math.sin(ang), f"{(90 + 45 * k) % 360}°", ha="center", va="center", fontsize=8,
           color=INK2)
a.set_xlim(-122, 122)
a.set_ylim(-122, 122)
a.set_aspect("equal")
a.set_xlabel("Re s")
a.set_ylabel("Im s")
a.set_title("(a) Oito cópias em torno do 0: uma estrela de 8 braços")
a.legend(loc="upper left", fontsize=8, frameon=True, facecolor=SURF, edgecolor=GRID)

b = ax[0, 1]
b.axvspan(0, 1, color=AZUL, alpha=0.07, lw=0, zorder=0)
b.text(0.97, 1.0, "reta crítica\nde ζ (cópia 0)", fontsize=8, color=AZUL, ha="right", va="bottom",
       bbox=dict(boxstyle="round,pad=0.2", fc=SURF, ec="none"))
v = [D["octogono"]["raio_vertice"] * np.exp(1j * (math.pi / 8 + k * math.pi / 4)) for k in range(9)]
b.fill([x.real for x in v], [x.imag for x in v], color=VIOLETA, alpha=0.12, lw=0, zorder=1)
for k in range(8):
    p = reta(k, 5)
    b.plot(p.real, p.imag, color=AZUL if k == 0 else INK2, lw=1.8 if k == 0 else 0.9, zorder=2)
th = np.linspace(0, 2 * math.pi, 400)
b.plot(0.5 * np.cos(th), 0.5 * np.sin(th), color=INK2, lw=0.8, ls="--", zorder=2)
rm = D["raio_max_cruzamento"]
b.plot(rm * np.cos(th), rm * np.sin(th), color=INK2, lw=0.8, ls=":", zorder=2)
b.plot([0], [0], "o", ms=5, color=INK, zorder=4)
b.text(0.06, 0.06, "0", fontsize=9)
b.text(-1.55, 1.55, f"violeta: octógono regular de apótema ½\ncercado pelas 8 retas críticas copiadas\n"
       f"tracejado: |s| = ½    pontilhado: |s| = {rm:.3f}\n(todo cruzamento de duas retas fica dentro)"
       .replace(".", ","), fontsize=7.8, color=INK2, va="top",
       bbox=dict(boxstyle="round,pad=0.3", fc=SURF, ec=GRID))
b.text(1.55, -1.42, f"zero mais perto do 0:\n|s| = {D['menor_modulo_de_zero']:.2f}".replace(".", ","), fontsize=8.5,
       color=INK, ha="right", va="bottom")
b.set_xlim(-1.6, 1.6)
b.set_ylim(-1.6, 1.6)
b.set_aspect("equal")
b.set_xlabel("Re s")
b.set_ylabel("Im s")
b.set_title("(b) Perto do 0: as retas se cruzam, mas não há zeros")

c = ax[1, 0]
c.axvspan(-0.5, 0.5, color=AZUL, alpha=0.06, lw=0, zorder=0)
c.axvline(0.5, color=AZUL, lw=1.2, zorder=1)
c.axvline(-0.5, color=CINZA, lw=1.2, zorder=1)
c.axvline(0, color=INK2, lw=0.8, ls="--", zorder=1)
alt = [z.imag for z in zs if z.imag > 0]
c.plot([0.5] * len(alt), alt, "o", ms=4.5, color=AZUL, zorder=3, label="zeros de ζ na reta (cópia k)")
c.plot([-0.5] * len(alt), alt, "o", ms=4.5, color=CINZA, zorder=3, label="os mesmos, vindos da cópia k + 4")
for nome, cor, rot in (("Epstein m²+5n²", VIOLETA, "Epstein m² + 5n²"), ("Davenport–Heilbronn", AQUA,
                                                                          "Davenport–Heilbronn")):
    for i, q in enumerate(EX[nome][:1]):
        xs = q["no_zero"]["desvios_no_braco"]
        c.plot(xs, [q["gama"]] * 4, "D", ms=6.5, color=cor, mec=SURF, mew=1, zorder=4,
               label=f"1º quarteto fora da reta de {rot}\n(outra função, mesma simetria s ↔ 1 − s)")
q = EX["Epstein m²+5n²"][0]
c.annotate("os 4 pontos ±½ ± b\n(b = 0,433)", (0.5 + q["b"], q["gama"]), xytext=(0, 30), textcoords="offset points",
           ha="center", fontsize=8.5, arrowprops=dict(arrowstyle="-", color=INK2, lw=0.7))
c.text(-0.03, 42, "eixo do braço (raio a 90° + 45°k)", fontsize=8, color=INK2, rotation=90, ha="right", va="center")
c.set_yscale("log")
c.set_ylim(10, 420)
c.set_xlim(-1.3, 1.3)
c.set_xlabel("desvio do eixo do braço")
c.set_ylabel("distância ao 0 ao longo do braço")
c.set_title("(c) Um braço visto de dentro: corredor de largura 1")
c.legend(loc="upper left", fontsize=7.8, frameon=True, facecolor=SURF, edgecolor=GRID)

d = ax[1, 1]
x = np.logspace(0, 3.6, 400)
dd = np.degrees(2 * np.arctan(1 / x))
d.axvspan(26, 4000, color=AZUL, alpha=0.07, lw=0, zorder=0)
d.text(30, 8, "ζ: γ/b > 26 (kernel)", fontsize=8.5, color=AZUL)
d.plot(x, dd, color=INK, lw=1.8, zorder=2, label="lacuna pequena 2δ, δ = arctan(b/γ)")
d.plot(x, 45 - dd, color=LARANJA, lw=1.6, zorder=2, label="lacuna grande, 8 cópias (16 pontos): 45° − 2δ")
d.plot(x, 90 - dd, color=VIOLETA, lw=1.6, ls="--", zorder=2, label="lacuna grande, 4 cópias (8 pontos): 90° − 2δ")
r16, r8 = D["dezesseis_regular_gama_sobre_b"], D["octogono_regular_gama_sobre_b"]
d.plot([r16], [22.5], "o", ms=8, color=LARANJA, mec=SURF, mew=1.5, zorder=4)
d.annotate(f"16-ágono regular\nγ/b = cot(π/16) = {r16:.3f}".replace(".", ","), (r16, 22.5), xytext=(10, 10),
           textcoords="offset points", fontsize=8)
d.plot([r8], [45], "o", ms=8, color=VIOLETA, mec=SURF, mew=1.5, zorder=4)
d.annotate(f"octógono regular\nγ/b = 1 + √2 = {r8:.3f}".replace(".", ","), (r8, 45), xytext=(10, 6),
           textcoords="offset points", fontsize=8)
for nome, cor in (("Epstein m²+5n²", VIOLETA), ("Davenport–Heilbronn", AQUA)):
    g = [q["gama_sobre_b"] for q in EX[nome]]
    d.plot(g, [q["no_meio"]["lacunas_16_graus"][0] for q in EX[nome]], "D", ms=6, color=cor, mec=SURF, mew=1,
           zorder=4)
d.set_xscale("log")
d.set_xlim(1, 4000)
d.set_ylim(0, 92)
d.set_xlabel("γ/b")
d.set_ylabel("lacuna entre pontos vizinhos da órbita (graus)")
d.set_title("(d) Em torno de ½: quando a órbita seria um polígono regular")
d.legend(loc="center right", bbox_to_anchor=(1, 0.71), fontsize=7.8, frameon=True, facecolor=SURF, edgecolor=GRID)

fig.tight_layout()
fig.savefig("oito_copias.png", dpi=150)
print("ok")
