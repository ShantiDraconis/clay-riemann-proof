"""Figura só com as escalas acima do verificado (10¹⁹ até o googolplex; 10↑↑4 no texto). Previsão, não cálculo."""
import json

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

SURF, INK, INK2, GRID, BLUE = "#fcfcfb", "#0b0b0b", "#52514e", "#e4e3df", "#2a78d6"
plt.rcParams.update({
    "figure.facecolor": SURF, "axes.facecolor": SURF, "savefig.facecolor": SURF, "axes.edgecolor": GRID,
    "axes.labelcolor": INK2, "xtick.color": INK2, "ytick.color": INK2, "text.color": INK, "axes.grid": True,
    "grid.color": GRID, "grid.linewidth": 0.6, "axes.spines.top": False, "axes.spines.right": False,
    "font.size": 9.5, "axes.titlesize": 10.5, "axes.titleweight": "bold", "axes.titlelocation": "left",
})
d = [r for r in json.load(open("acima.json")) if r["altura"] != "10↑↑4"]
nomes = [r["altura"] for r in d]
x = list(range(len(d)))


def br(v, f):
    return format(v, f).replace(".", ",")


fig, axs = plt.subplots(3, 1, figsize=(12, 12.5), gridspec_kw={"hspace": 0.55})
ax = axs[0]
y = [float(r["menos_log10_lambda_min"]) for r in d]
ax.plot(x, y, color=BLUE, lw=1, alpha=0.5)
ax.plot(x, y, ls="none", color=BLUE, marker="o", markersize=8, markeredgecolor=SURF, markeredgewidth=2)
ax.set_yscale("log")
for i, v in enumerate(y):
    ax.annotate(f"10^−{br(v, '.3g')}", (i, v), xytext=(0, 8), textcoords="offset points", ha="center", fontsize=7.5,
                color=INK2)
ax.set_ylabel("−log₁₀ |λ| do par mais frágil")
ax.set_title("(a) Quão perto de colidir chega o par mais frágil entre todos os zeros até T (previsão GUE: λ ≈ −Δγ²/2)")

ax = axs[1]
y = [float(r["altura_media_entre_eles"]) for r in d]
ax.plot(x, y, color=BLUE, lw=1, alpha=0.5)
ax.plot(x, y, ls="none", color=BLUE, marker="o", markersize=8, markeredgecolor=SURF, markeredgewidth=2)
ax.set_yscale("log")
for i, (v, r) in enumerate(zip(y, d)):
    ax.annotate(br(v, ".2g"), (i, v), xytext=(0, 8), textcoords="offset points", ha="center", fontsize=7.5, color=INK2)
ax.set_ylabel("altura média entre dois deles")
ax.set_title("(b) Pares mais frágeis que o recorde já visto (λ < −4,59·10⁻⁷): de 1 a cada 5·10⁵ de altura "
             "a praticamente todo par")

ax = axs[2]
y = [float(r["w_sem_zeros"]) for r in d]
ax.plot(x, y, color=BLUE, lw=1, alpha=0.5)
ax.plot(x, y, ls="none", color=BLUE, marker="o", markersize=8, markeredgecolor=SURF, markeredgewidth=2)
ax.set_yscale("log")
for i, (v, r) in enumerate(zip(y, d)):
    ax.annotate(br(v, ".2g"), (i, v), xytext=(0, 8), textcoords="offset points", ha="center", fontsize=7.5, color=INK2)
ax.set_ylabel("largura excluída w")
ax.set_title("(c) Onde um zero fora da reta ainda pode estar: b = |Re s − ½| < ½ − w (região sem zeros provada)")
for a in axs:
    a.set_title(a.get_title(loc="left"), loc="left", pad=22)
    lo, hi = a.get_ylim()
    a.set_ylim(lo, hi * 1e3 if hi > 1 else hi * 30)
    a.set_xticks(x)
    a.set_xticklabels(nomes)
    a.set_xlabel("altura T (acima de 10¹⁸: nenhum trecho contínuo verificado)")
fig.suptitle("Só acima do verificado: o que se espera dos zeros de ζ acima de 10¹⁸ "
             "(previsão e cotas, não cálculo)", x=0.06, ha="left", fontsize=12.5, fontweight="bold")
fig.text(0.06, 0.005, "Até 8,1·10³⁴ só há janelas isoladas calculadas (Odlyzko, Gourdon, Bober–Hiary), todas na reta. "
         "Em 10↑↑4: λ do par mais frágil ≈ −10^(−6,7·10⁹⁹⁹⁹⁹), w ≈ 7,9·10^(−6 666 666 673). Dados: acima.json.",
         fontsize=8.5, color=INK2)
fig.savefig("acima.png", dpi=150, bbox_inches="tight")
print("ok")
