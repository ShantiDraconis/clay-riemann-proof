"""Figura dos quase-encontros nos 14 380 683 zeros contíguos (3 000 175 342 471,5 a 3 000 178 702 471,5)."""
import json
import math

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

SURF, INK, INK2, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#e4e3df"
BLUE, ORANGE, AQUA, GRAY = "#2a78d6", "#eb6834", "#1baf7a", "#9a9890"
plt.rcParams.update({
    "figure.facecolor": SURF, "axes.facecolor": SURF, "savefig.facecolor": SURF, "axes.edgecolor": GRID,
    "axes.labelcolor": INK2, "xtick.color": INK2, "ytick.color": INK2, "text.color": INK, "axes.grid": True,
    "grid.color": GRID, "grid.linewidth": 0.6, "axes.spines.top": False, "axes.spines.right": False,
    "font.size": 9.5, "axes.titlesize": 10.5, "axes.titleweight": "bold", "axes.titlelocation": "left",
    "legend.frameon": False, "legend.fontsize": 8.5,
})
d = json.load(open("aproximacoes.json"))


def br(v, f):
    return format(v, f).replace(".", ",")


fig, axs = plt.subplots(2, 2, figsize=(13.5, 10), gridspec_kw={"hspace": 0.42, "wspace": 0.3})

# (a) a cauda
ax = axs[0, 0]
c = d["cauda"]
x = np.array([r["x"] for r in c])
F = np.array([r["F"] for r in c])
xx = np.logspace(-3, 0, 200)
gue = np.array([r["GUE"] for r in c])
ax.plot(x, gue, color=GRAY, lw=2, label="GUE (repulsão cúbica, ≈ 1,08 x³)")
ax.plot(xx, math.pi ** 2 / 12 * xx ** 2, color=GRAY, lw=1.2, ls="--", label="GOE (≈ x²)")
ax.plot(xx, 1 - np.exp(-xx), color=GRAY, lw=1.2, ls=":", label="ao acaso, Poisson (≈ x)")
m = F > 0
ax.plot(x[m], F[m], ls="none", marker="o", markersize=7, color=BLUE, markeredgecolor=SURF, markeredgewidth=1.5,
        label="ζ, 14 380 682 espaçamentos")
ax.set_xscale("log")
ax.set_yscale("log")
ax.set_ylim(1e-8, 1.2)
ax.set_xlabel("x (espaçamento normalizado)")
ax.set_ylabel("fração de espaçamentos com s < x")
ax.set_title(f"(a) A cauda é cúbica: expoente {br(d['expoente_cauda_0.01_0.1'], '.2f')} (GUE: 3,00)")
ax.legend(loc="lower right")

# (b) o menor espaçamento em n zeros
ax = axs[0, 1]
b = d["minimo_por_bloco"]
n = np.array([r["n"] for r in b])
med = np.array([r["mediana_do_minimo"] for r in b])
nn = np.logspace(3, 30, 100)
ax.plot(nn, (math.log(2) * 9 / (math.pi ** 2 * nn)) ** (1 / 3), color=GRAY, lw=1.5, ls="--",
        label="GUE: (9 ln 2 / (π² n))^(1/3)")
ax.plot(n, med, ls="none", marker="o", markersize=7, color=BLUE, markeredgecolor=SURF, markeredgewidth=1.5,
        label="ζ: mediana do menor s em blocos de n zeros")
for k, s in [(6.3e8, 1e-3), (6.3e17, 1e-6), (6.3e29, 1e-10)]:
    ax.annotate(f"s = {br(s, 'g')} em ~{br(k, '.1e')} zeros", (k, s), xytext=(6, 4), textcoords="offset points",
                fontsize=8, color=INK2)
ax.set_xscale("log")
ax.set_yscale("log")
ax.set_xlabel("n (zeros seguidos)")
ax.set_ylabel("menor espaçamento normalizado")
ax.set_title("(b) O par mais próximo encolhe como n^(−1/3), sem chegar a 0")
ax.legend(loc="upper right")

# (c) o que acontece em volta: os vizinhos se afastam
ax = axs[1, 0]
v = d["vizinhos"]
cent = [(r["s_do_par"][0] + r["s_do_par"][1]) / 2 for r in v]
ax.plot(cent, [r["media_dos_vizinhos"] for r in v], marker="o", color=BLUE, lw=2, markeredgecolor=SURF,
        markeredgewidth=1.5, label="espaçamento médio dos dois vizinhos")
ax.plot(cent, [r["soma_vizinho_par_vizinho"] for r in v], marker="s", color=ORANGE, lw=2, markeredgecolor=SURF,
        markeredgewidth=1.5, label="vizinho + par + vizinho")
ax.axhline(1, color=GRAY, lw=1, ls="--")
ax.axhline(3, color=GRAY, lw=1, ls=":")
ax.set_xscale("log")
ax.set_xlabel("espaçamento s do par")
ax.set_ylabel("em espaçamentos médios")
ax.set_title("(c) Num quase-encontro os vizinhos se afastam (1,39 em vez de 1)")
ax.legend(loc="center right")

# (d) os 30 pares mais próximos
ax = axs[1, 1]
p = d["pares_mais_proximos"]
tt = [(float(r["t"]) - 3.0001753424715e12) / 1e6 for r in p]
ss = [r["s"] for r in p]
ax.scatter(tt, ss, s=40, color=BLUE, edgecolor=SURF, linewidth=1.2, zorder=3)
for r, t_, s_ in list(zip(p, tt, ss))[:3]:
    dir_ = t_ > 1.5
    ax.annotate(f"{r['zeros'][0]}: s = {br(s_, '.4f')}, λ = {br(r['lambda_colisao'], '.2e')}", (t_, s_),
                xytext=(-8 if dir_ else 8, -3), textcoords="offset points", fontsize=8, color=INK,
                ha="right" if dir_ else "left")
ax.set_yscale("log")
ax.set_xlabel("t − 3 000 175 342 471,5 (milhões)")
ax.set_ylabel("espaçamento normalizado s")
ax.set_title("(d) Os 30 pares mais próximos: todos na reta, nenhum colidiu")
fig.suptitle("Onde os zeros de ζ quase se juntam: 14 380 683 zeros contíguos acima de 3·10¹² (análises completas)",
             x=0.06, ha="left", fontsize=12.5, fontweight="bold")
fig.savefig("quase_encontros.png", dpi=150, bbox_inches="tight")
# tabela CSV dos 30 pares
with open("pares_mais_proximos.csv", "w") as f:
    f.write("zero_k,zero_k1,t,Delta_gamma,s,lambda_colisao,s_vizinho_antes,s_vizinho_depois,S_depois_do_par\n")
    for r in p:
        f.write(f"{r['zeros'][0]},{r['zeros'][1]},{r['t']},{r['Delta_gamma']:.6e},{r['s']:.6f},{r['lambda_colisao']:.4e},"
                f"{r['s_vizinho_antes']:.4f},{r['s_vizinho_depois']:.4f},{r['S_depois_do_par']:.4f}\n")
print("ok")
