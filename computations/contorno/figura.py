"""Figura: o primeiro zero medido no círculo e no quadrado.

    python3 figura.py      (lê contornos.json; grava contornos.png)

(a) |ζ| em volta de z₀ = ½ + 14,1347251417 i, com o círculo de raio 0,4 e o quadrado de meio-lado 0,4, onde |ζ| é
    máximo em cada um, e as bolas de unicidade que cada cota dá.
(b) max |ζ| no contorno contra o raio: círculo e quadrado medidos, e as cotas que o kernel tem (240 e cotaQ).
(c) A distância que cada medida certifica (raio da bola de unicidade) contra as distâncias de ρ₁.
(d) Quantas avaliações certificadas cada cota pede: cobrir o anel R ≤ |s − z₀| ≤ 0,2 sem zeros, e certificar a
    própria cota no contorno.
"""
import json
import math

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.colors import LinearSegmentedColormap

from zeta_em import zeta

SURF, INK, INK2, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#e4e3df"
CIRC, QUAD = "#2a78d6", "#eb6834"
NEUTRO = "#8a8984"
plt.rcParams.update({
    "figure.facecolor": SURF, "axes.facecolor": SURF, "savefig.facecolor": SURF, "axes.edgecolor": GRID,
    "axes.labelcolor": INK2, "xtick.color": INK2, "ytick.color": INK2, "text.color": INK, "axes.grid": True,
    "grid.color": GRID, "grid.linewidth": 0.6, "axes.spines.top": False, "axes.spines.right": False,
    "font.size": 9.5, "axes.titlesize": 10.5, "axes.titleweight": "bold", "axes.titlelocation": "left",
    "legend.frameon": False, "legend.fontsize": 8.5,
})
D = json.load(open("contornos.json"))
T0 = D["z0"][1]
cont = D["contornos"]
trans = {t["fonte"]: t for t in D["transferencia"]}


def lin(forma, campo):
    xs = [c for c in cont if c["forma"] == forma]
    return [c["raio"] for c in xs], [c[campo] for c in xs]


fig, ax = plt.subplots(2, 2, figsize=(12.5, 9.4))

# (a) mapa
a = ax[0, 0]
x = np.linspace(-0.05, 1.05, 260)
y = np.linspace(T0 - 0.55, T0 + 0.55, 260)
X, Y = np.meshgrid(x, y)
V = np.abs(zeta(X + 1j * Y))
cinza = LinearSegmentedColormap.from_list("cinza", ["#fcfcfb", "#e4e3df", "#b9b8b2", "#8a8984", "#52514e"])
im = a.pcolormesh(x - 0.5, y - T0, V, cmap=cinza, shading="auto", vmin=0, vmax=0.75, zorder=0)
cb = fig.colorbar(im, ax=a, fraction=0.04, pad=0.02)
cb.set_label("|ζ(s)|", color=INK2)
cb.outline.set_visible(False)
th = np.linspace(0, 2 * math.pi, 400)
a.plot(0.4 * np.cos(th), 0.4 * np.sin(th), color=CIRC, lw=2.4, label="círculo |s − z₀| = 0,4")
a.plot([0.4, -0.4, -0.4, 0.4, 0.4], [-0.4, -0.4, 0.4, 0.4, -0.4], color=QUAD, lw=2.4, label="quadrado de meio-lado 0,4")
for forma, cor in (("circulo", CIRC), ("quadrado", QUAD)):
    c = next(c for c in cont if c["forma"] == forma and c["raio"] == 0.4)
    a.plot(*c["onde"], "o", ms=8, color=cor, mec=SURF, mew=2, zorder=5)
    a.annotate(f"máx {c['max_medido']:.3f}".replace(".", ","), c["onde"], xytext=(8, -4 if forma == "circulo" else 6),
               textcoords="offset points", fontsize=8.5, color=INK)
Ri = D["R_ideal"]
a.plot(Ri * np.cos(th), Ri * np.sin(th), color=INK2, lw=1, ls=":")
a.text(0.05, -Ri * 1.06, f"bola ideal, R = {Ri:.3f}".replace(".", ","), fontsize=8, color=INK)
a.plot(0, 0, "x", color=INK, ms=7, mew=1.6)
a.text(0.02, 0.025, "ρ₁", fontsize=9, color=INK)
a.axvline(-0.5, color=INK2, lw=0.8, ls="--")
a.text(-0.49, -0.52, "Re s = 0", fontsize=8, color=INK)
a.set_xlim(-0.55, 0.55)
a.set_ylim(-0.55, 0.55)
a.set_aspect("equal")
a.set_xlabel("Re s − ½")
a.set_ylabel("Im s − 14,1347251417")
a.set_title("(a) |ζ| perto de ρ₁ e os dois contornos")
a.legend(loc="upper right", fontsize=8, frameon=True, facecolor=SURF, edgecolor=GRID, framealpha=0.9)

# (b) máximo no contorno
b = ax[0, 1]
for forma, cor, nome in (("circulo", CIRC, "círculo (medido)"), ("quadrado", QUAD, "quadrado (medido)")):
    r, m = lin(forma, "max_medido")
    b.semilogy(r, m, "o-", color=cor, lw=2, ms=6, mec=SURF, mew=1.5, label=nome)
rr = np.linspace(0.05, 0.4, 50)
b.semilogy(rr, D["abs_zeta1"] * rr, color=INK2, lw=1, ls="--", label="|ζ′(ρ₁)|·raio (linear)")
r, q = lin("circulo", "cotaQ")
b.semilogy(r, q, color=NEUTRO, lw=1.6, label="cotaQ do kernel (N = 6, M = 10)")
b.axhline(240, color=INK, lw=1.2, ls="-.")
b.text(0.06, 280, "240: a cota da §47 (Euler–Maclaurin de ordem 1)", fontsize=8, color=INK)
b.set_ylim(0.02, 900)
b.set_xlabel("raio do círculo / meio-lado do quadrado")
b.set_ylabel("cota de |ζ| no contorno (escala log)")
b.set_title("(b) A cota no contorno: medida contra a do kernel")
b.legend(loc="center right", fontsize=8)

# (c) distâncias
c = ax[1, 0]
kh = D["kernel_hoje"]
barras = [("kernel §47: cota 240", 1e-6, NEUTRO, False),
          ("máximo possível com 240", kh["R_maximo_com_F2"], NEUTRO, True),
          ("kernel §48: cotaQ 7,64", 2e-3, NEUTRO, False),
          ("kernel §48: quadrado, cota 1", 9 / 625, QUAD, False),
          ("quadrado medido + 25%", trans["quadrado medido +25%"]["R_encaixado"], QUAD, True),
          ("círculo medido + 25%", trans["círculo medido +25%"]["R_encaixado"], CIRC, True),
          ("ideal: |ζ′ − c| ≤ |c|/2", D["R_ideal"], INK2, True)]
ys = np.arange(len(barras))[::-1]
SUP = str.maketrans("-0123456789", "⁻⁰¹²³⁴⁵⁶⁷⁸⁹")


def fmt(v):
    e = math.floor(math.log10(v))
    if e >= -3:
        return f"{v:.2g}".replace(".", ",")
    m = v / 10 ** e
    return ("" if abs(m - 1) < 1e-9 else f"{m:.1f}".replace(".", ",") + "·") + "10" + str(e).translate(SUP)


for yv, (nome, v, cor, so_flutuante) in zip(ys, barras):
    if so_flutuante:
        c.barh(yv, v, left=1e-7, height=0.6, color=SURF, edgecolor=cor, hatch="////", lw=1.2, zorder=2)
    else:
        c.barh(yv, v, left=1e-7, height=0.6, color=cor, zorder=2)
    if v > 0.3:
        c.text(v / 1.3, yv, fmt(v), va="center", ha="right", fontsize=8.5, color=INK,
               bbox=dict(boxstyle="round,pad=0.15", fc=SURF, ec="none"))
    else:
        c.text(v * 1.4, yv, fmt(v), va="center", fontsize=8.5, color=INK)
c.set_yticks(ys, [b_[0] for b_ in barras], fontsize=8.5)
c.set_xscale("log")
c.set_xlim(1e-7, 60)
dist = D["distancias"]
for nome, v in (("altura 13", dist["altura_13"]), ("ρ₂", dist["rho2"]), ("polo s = 1", dist["polo_s_igual_1"])):
    c.axvline(v, color=INK2, lw=1, ls="--", zorder=1)
    c.text(v * 1.08, ys[0] + 0.45, nome, fontsize=8, color=INK2, rotation=90, va="top")
c.set_xlabel("raio da bola de unicidade em volta de z₀ (escala log)")
c.set_title("(c) Raio da bola de unicidade (cheia: kernel; listrada: flutuante)")
c.grid(axis="y", visible=False)

# (d) custo
d = ax[1, 1]
pts = [("cotaQ", trans["cotaQ no disco"]["B"], trans["cotaQ no disco"]["cobertura_simulada"], NEUTRO),
       ("quadrado", trans["quadrado medido +25%"]["B"], trans["quadrado medido +25%"]["cobertura_simulada"], QUAD),
       ("círculo", trans["círculo medido +25%"]["B"], trans["círculo medido +25%"]["cobertura_simulada"], CIRC)]
for nome, B, n, cor in pts:
    d.loglog(B, n, "o", ms=9, color=cor, mec=SURF, mew=2, zorder=4)
    if nome == "cotaQ":
        d.annotate("anel, cotaQ: " + f"{n:,}".replace(",", " "), (B, n), xytext=(9, -3), textcoords="offset points",
                   fontsize=8.5)
B240 = trans["ATK 240 (ordem 1)"]
d.loglog(240, kh["cobertura_formula"], "o", ms=9, mfc=SURF, mec=INK2, mew=1.6, zorder=4)
d.annotate("240: ≈ 5·10⁷ (estimativa)", (240, kh["cobertura_formula"]), xytext=(-150, -4),
           textcoords="offset points", fontsize=8.5)
d.loglog(1.0, 150, "s", ms=9, color=QUAD, mec=INK, mew=1.4, zorder=5)
d.annotate("cota 1 certificada no kernel (§48): 150", (1.0, 150), xytext=(12, 2), textcoords="offset points",
           fontsize=8.5)
d.loglog(1.0, 376, "o", ms=9, color=QUAD, mec=INK, mew=1.4, zorder=5)
d.annotate("anel com a cota 1: 376", (1.0, 376), xytext=(12, 4), textcoords="offset points", fontsize=8.5)
for forma, cor in (("circulo", CIRC), ("quadrado", QUAD)):
    cc = next(c_ for c_ in cont if c_["forma"] == forma and c_["raio"] == 0.4)
    d.loglog(cc["B_25"], cc["custo"]["avaliacoes"], "s", ms=8, color=cor, mec=SURF, mew=2, zorder=4)
ft = {f: next(c_ for c_ in cont if c_["forma"] == f and c_["raio"] == 0.4)["custo"]["avaliacoes"]
      for f in ("circulo", "quadrado")}
d.text(0.1, 4e6, "ponto flutuante, cota + 25%:\n"
       f"  ● anel: círculo {pts[2][2]}, quadrado {pts[1][2]}\n"
       f"  ■ certificar a cota: círculo {ft['circulo']}, quadrado {ft['quadrado']}", fontsize=8.5, color=INK2,
       va="top")
d.set_xlim(0.08, 2000)
d.set_ylim(50, 3e8)
d.set_xlabel("cota B de |ζ| no disco de raio 0,4 (escala log)")
d.set_ylabel("avaliações certificadas (escala log)")
d.set_title("(d) Avaliações no kernel: anel sem zeros (●), cota (■)")
fig.tight_layout()
fig.savefig("contornos.png", dpi=150)
print("ok")
