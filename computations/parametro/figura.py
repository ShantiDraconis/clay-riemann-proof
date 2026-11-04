"""Figura: o mesmo padrão dos dois lados da reta (o parâmetro κ), nos zeros fora da reta de verdade.

    python3 figura.py          (lê lombadas.json e ../aproximacoes/pares_mais_proximos.csv; grava padrao_fora.png)

(a) Davenport–Heilbronn na reta perto do zero fora ½ + 0,3085 + 85,699i: Z não troca de sinal, faz uma lombada, e a
    forma local Z_min + Z''(t − t_m)²/2 dá b = √(2|Z_min|/|Z''|).
(b) Epstein m² + 5n²: a contagem só da reta (S_reta) cai 2 a cada par fora; somando 2 por par (S) volta a oscilar em
    torno de 0. Foi assim que o par 0,81117 + 58,50774i, que a malha tinha pulado, apareceu.
(c) b lido da lombada contra o b verdadeiro (as duas funções).
(d) κ em unidades de espaçamento²: ζ (κ = (s/2)² > 0, os 30 pares mais apertados de 14 380 683 zeros) e os zeros fora
    da reta das duas funções (κ = −b² < 0). Em κ = 0 o par é um zero duplo.
"""
import csv
import json
import sys

sys.path.insert(0, "/home/claude/ext/mpmath")
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from mpmath import mp, mpf, mpc, sqrt, dirichlet, loggamma, log, pi, exp

SURF, INK, INK2, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#e4e3df"
CORES = ["#0d366b", "#2a78d6", "#1baf7a", "#eda100", "#eb6834"]
C_ZETA, C_DH, C_EP = CORES[0], CORES[1], CORES[3]
plt.rcParams.update({
    "figure.facecolor": SURF, "axes.facecolor": SURF, "savefig.facecolor": SURF, "axes.edgecolor": GRID,
    "axes.labelcolor": INK2, "xtick.color": INK2, "ytick.color": INK2, "text.color": INK, "axes.grid": True,
    "grid.color": GRID, "grid.linewidth": 0.6, "axes.spines.top": False, "axes.spines.right": False,
    "font.size": 9.5, "axes.titlesize": 10.5, "axes.titleweight": "bold", "axes.titlelocation": "left",
    "legend.frameon": False, "legend.fontsize": 8.5,
})
L = json.load(open("lombadas.json"))
dh, ep = L["dh"], L["epstein"]

# (a) Z de Davenport–Heilbronn
mp.dps = 15
kap = (sqrt(10 - 2 * sqrt(5)) - 2) / (sqrt(5) - 1)
CHI5, CHI5B = [0, 1, 1j, -1j, -1], [0, 1, -1j, 1j, -1]
f = lambda s: (1 - 1j * kap) / 2 * dirichlet(s, CHI5) + (1 + 1j * kap) / 2 * dirichlet(s, CHI5B)
theta = lambda t: t / 2 * log(5 / pi) + loggamma(mpf(3) / 4 + 1j * t / 2).imag
z0 = exp(1j * theta(mpf("10.3"))) * f(mpc(0.5, mpf("10.3")))
fase = z0 / abs(z0)
Z = lambda t: float((exp(1j * theta(mpf(t))) * f(mpc(0.5, t)) / fase).real)
ts = [81.5 + 0.025 * j for j in range(361)]
zs = [Z(t) for t in ts]

fig, ax = plt.subplots(2, 2, figsize=(11.5, 8.2))
a = ax[0, 0]
a.axhline(0, color=INK2, lw=0.8)
a.plot(ts, zs, color=C_DH, lw=2, label="Z na reta")
r = dh["fora"][0]
tm, zm, z2 = r["t_lombada"], r["Z_lombada"], r["Z_seg"]
tl = [t for t in ts if abs(t - tm) < 0.55]
a.plot(tl, [zm + z2 / 2 * (t - tm) ** 2 for t in tl], color=C_EP, lw=2, ls="--",
       label="forma local")
ta, tb = r["vao_na_reta"]
a.axvspan(ta, tb, color=GRID, alpha=0.6, lw=0)
zr = [x for x in json.load(open("dh.json"))["zeros"] if ts[0] <= x <= ts[-1]]
a.plot(zr, [0] * len(zr), "o", ms=6, color=C_DH, mec=SURF, mew=1.5, label="zeros na reta")
a.axvline(r["rho"][1], color=INK2, lw=0.8, ls=":")
a.annotate((f"zero fora: ½ + {r['b']:.4f} + {r['rho'][1]:.3f}i\nvão na reta: {r['vao_em_espacamentos_medios']:.2f} "
            f"espaçamentos\nb da lombada = {r['b_lombada']:.4f}").replace(".", ","), xy=(tm, zm), xytext=(83.35, 3.75), fontsize=8.5, va="top",
           color=INK, arrowprops=dict(arrowstyle="-", color=INK2, lw=0.8))
a.set_xlabel("t")
a.set_ylabel("Z(t)")
a.set_ylim(-5.4, 4.0)
a.set_title("(a) A reta vê o par fora como lombada sem troca de sinal")
a.legend(loc="lower right")

# (b) contagem de Epstein
b_ = ax[0, 1]
T = [x["T"] for x in ep["serie"]]
b_.plot(T, [x["S_reta"] for x in ep["serie"]], color=C_EP, lw=2, label="S só da reta (N_reta − θ/π − 1)")
b_.plot(T, [x["S"] for x in ep["serie"]], color=C_ZETA, lw=2, label="S com 2 por par fora (N_reta + 2k − θ/π − 1)")
for x in ep["fora"]:
    b_.axvline(x["rho"][1], color=GRID, lw=1.2, zorder=0)
b_.axhline(0, color=INK2, lw=0.8)
b_.annotate("par achado pela contagem:\n0,81117 + 58,50774i", xy=(58.51, -12.5), xytext=(63, -6), fontsize=8.5,
            arrowprops=dict(arrowstyle="-", color=INK2, lw=0.8))
b_.set_xlabel("T")
b_.set_ylabel("S(T)")
b_.set_title("(b) Epstein m² + 5n²: −2 por par fora; 13 pares fecham a conta")
b_.legend(loc="lower left")

# (c) b da lombada contra b
c = ax[1, 0]
c.plot([0, 0.5], [0, 0.5], color=INK2, lw=0.8, ls=":")
for nome, d, cor in (("Davenport–Heilbronn", dh, C_DH), ("Epstein m² + 5n²", ep, C_EP)):
    xs = [x["b"] for x in d["fora"] if x["b_lombada"]]
    ys = [x["b_lombada"] for x in d["fora"] if x["b_lombada"]]
    c.plot(xs, ys, "o", ms=8, color=cor, mec=SURF, mew=1.5, label=nome)
sem = [x["b"] for x in ep["fora"] if not x["b_lombada"]]
c.plot(sem, [0.02] * len(sem), "x", ms=8, color=C_EP, mew=2, label="sem mínimo de |Z| no vão (b ≥ 0,345)")
c.set_xlim(0, 0.5)
c.set_ylim(0, 0.7)
c.set_xlabel("b verdadeiro (Re ρ − ½)")
c.set_ylabel("b lido da lombada √(2|Z_min|/|Z''|)")
c.set_title("(c) b sai da lombada; erro < 2 % para b ≤ 0,2")
c.legend(loc="upper left")

# (d) κ dos dois lados
d = ax[1, 1]
zeta = [float(row["s"]) for row in csv.DictReader(open("../aproximacoes/pares_mais_proximos.csv"))]
d.plot([(s / 2) ** 2 for s in zeta], [2] * len(zeta), "o", ms=7, color=C_ZETA, mec=SURF, mew=1.2, alpha=0.9,
       label="ζ (30 pares): κ = (s/2)²")
d.plot([x["kappa_em_espacamentos2"] for x in dh["fora"]], [1] * len(dh["fora"]), "o", ms=8, color=C_DH, mec=SURF,
       mew=1.2, label="DH fora: κ = −b²")
d.plot([x["kappa_em_espacamentos2"] for x in ep["fora"]], [0] * len(ep["fora"]), "o", ms=8, color=C_EP, mec=SURF,
       mew=1.2, label="Epstein fora: κ = −b²")
d.axvline(0, color=INK, lw=1)
d.set_xscale("symlog", linthresh=1e-6)
d.set_xlim(-1, 1e-1)
d.set_yticks([0, 1, 2], ["Epstein", "DH", "ζ"])
d.set_ylim(-0.5, 2.8)
d.text(2e-6, 2.35, "dois zeros na reta", fontsize=8.5, color=INK2)
d.text(-0.9, 2.35, "quarteto fora da reta", fontsize=8.5, color=INK2)
d.text(0, 2.55, "κ = 0: zero duplo", fontsize=8.5, color=INK, ha="center")
d.set_xlabel("κ em espaçamentos² (escala log simétrica)")
d.set_title("(d) O mesmo parâmetro κ dos dois lados")
d.legend(loc="center right", bbox_to_anchor=(1.0, 0.36), fontsize=8)
fig.tight_layout()
fig.savefig("padrao_fora.png", dpi=150)
print("ok")
