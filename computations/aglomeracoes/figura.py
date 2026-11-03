"""Figura: onde há zeros fora da reta de verdade, onde os de ζ chegam mais perto de sair e as aglomerações.

    python3 figura.py   (lê aglomeracoes.json, analogos_fora.json, zeta_ate_170.json, fronteira_resumo.json)
"""
import json
import math

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

SURF, INK, INK2, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#e4e3df"
BLUE, ORANGE, AQUA, GRAY = "#2a78d6", "#eb6834", "#1baf7a", "#9a9890"
plt.rcParams.update({
    "figure.facecolor": SURF, "axes.facecolor": SURF, "savefig.facecolor": SURF,
    "axes.edgecolor": GRID, "axes.labelcolor": INK2, "xtick.color": INK2, "ytick.color": INK2,
    "text.color": INK, "axes.grid": True, "grid.color": GRID, "grid.linewidth": 0.6,
    "axes.spines.top": False, "axes.spines.right": False, "font.size": 9.5, "axes.titlesize": 11,
    "axes.titleweight": "bold", "axes.titlelocation": "left", "legend.frameon": False, "legend.fontsize": 8.5,
})

ag = json.load(open("aglomeracoes.json"))
an = json.load(open("analogos_fora.json"))
zz = json.load(open("zeta_ate_170.json"))
fr = json.load(open("fronteira_resumo.json"))

fig, axs = plt.subplots(2, 2, figsize=(13.5, 10.8), gridspec_kw={"hspace": 0.52, "wspace": 0.24})


def br(x, f):
    return format(x, f).replace(".", ",")


# (a) zeros fora da reta de verdade: funções sem produto de Euler; ζ toda na reta
ax = axs[0, 0]
ax.axvline(0.5, color=INK2, lw=1, zorder=1)
ax.scatter([0.5] * len(zz), zz, s=10, color=BLUE, zorder=3, label=f"ζ: {len(zz)} zeros até Im 170, todos em Re = ½")
estilos = {"Davenport–Heilbronn": (ORANGE, "o"), "Epstein m²+5n²": (AQUA, "s"), "ζ(s)+ζ(s+1)": (GRAY, "D")}
for nome, d in an.items():
    cor, mk = estilos[nome]
    zs = d["zeros"]
    if not zs:
        continue
    xs = [z["re"] for z in zs]
    ys = [z["im"] for z in zs]
    ax.scatter(xs, ys, s=46, color=cor, marker=mk, edgecolor=SURF, linewidth=1.2, zorder=4,
               label=f"{nome} (até Im {d['ate_Im']}): {len(zs)}")
    if nome != "ζ(s)+ζ(s+1)":  # equação funcional: o espelho 1 − β + iγ também é zero
        ax.scatter([1 - v for v in xs], ys, s=40, facecolor=SURF, edgecolor=cor, marker=mk, linewidth=1.4, zorder=4)
    bmax = max(z["b"] for z in zs)
    for z in zs:
        if nome != "ζ(s)+ζ(s+1)":
            ax.plot([1 - z["re"], z["re"]], [z["im"], z["im"]], color=cor, lw=0.8, alpha=0.5, zorder=2)
        if nome == "Davenport–Heilbronn" or (nome == "Epstein m²+5n²" and z["b"] == bmax):
            ax.annotate(f"b = {br(z['b'], '.3f')}", (z["re"], z["im"]),
                        xytext=(6, -11) if nome == "Davenport–Heilbronn" else (6, 5), textcoords="offset points",
                        fontsize=7.5, color=INK2)
tt = [2 + i for i in range(170)]
ax.fill_betweenx(tt, [1 - 1 / (5.558691 * math.log(t)) for t in tt], [1.35] * len(tt), color=BLUE, alpha=0.07,
                 lw=0, label="região sem zeros de ζ (e o espelho perto de Re = 0)")
ax.fill_betweenx(tt, [0] * len(tt), [1 / (5.558691 * math.log(t)) for t in tt], color=BLUE, alpha=0.07, lw=0)
ax.set_xlim(0.0, 1.35)
ax.set_ylim(0, 175)
ax.set_xlabel("Re s")
ax.set_ylabel("Im s")
ax.set_title("(a) Zeros fora da reta existem — em funções sem produto de Euler")
ax.text(0.98, 0.97, "vazados: o espelho 1 − β + iγ\n(equação funcional)", transform=ax.transAxes, ha="right",
        va="top", fontsize=7.5, color=INK2)
ax.legend(loc="upper left", bbox_to_anchor=(0.0, -0.11), ncol=2)

# (b) onde os zeros de ζ chegam mais perto de sair da reta (todas as listas certificadas)
ax = axs[0, 1]
pts = []
for v in fr["varreduras"]:
    T = 10 ** v["expoente"] + v["deslocamento"]
    pts.append((T, -v["lambda_melhor"], f"10^{v['expoente']}"))
pts.append((3.000175407476e12, 4.593296e-07, "3·10¹² contínua"))
pts.append((3.000175339472e12, 3.1896e-05, "3·10¹² seção 13"))
ax.annotate("3·10¹², seção 13 (par #6)", (3.000175339472e12, 3.1896e-05), xytext=(8, -3), textcoords="offset points",
            fontsize=8, color=INK2)
xs = [p[0] for p in pts]
ys = [p[1] for p in pts]
ax.scatter(xs, ys, s=40, color=BLUE, edgecolor=SURF, linewidth=1.2, zorder=3)
melhor = sorted(pts, key=lambda p: p[1])[:3]
for T, l, nome in melhor:
    ax.annotate(f"{nome}: λ = −{br(l, '.2e')}", (T, l), xytext=(8, -3), textcoords="offset points", fontsize=8,
                color=INK)
ax.set_xscale("log")
ax.set_yscale("log")
ax.set_xlabel("altura T")
ax.set_ylabel("|λ| do par mais frágil (tempo de colisão, de Bruijn)")
ax.set_title("(b) Onde ζ chega mais perto de sair da reta: 9,9 milhões de zeros")
ax.text(0.10, 0.80, "mais para baixo = mais perto de colidir\nnenhum saiu da reta: déficit 0 em todas as janelas",
        transform=ax.transAxes, fontsize=8, color=INK2, va="top")

# (c) a aglomeração mais densa: 7 zeros em 3,66 espaçamentos, e S(t)
ax = axs[1, 0]
a0 = ag["aglomeracoes"][0]
d = ag["espacamento_medio"]
zs = a0["zeros"]
x = [z["t_rel"] / d for z in zs]
S = [z["S_depois"] for z in zs]
# S(t) entre zeros desce com inclinação 1 por espaçamento médio; sobe 1 em cada zero
for i in range(len(x) - 1):
    ax.plot([x[i], x[i + 1]], [S[i], S[i] - (x[i + 1] - x[i])], color=BLUE, lw=2, solid_capstyle="round")
    ax.plot([x[i + 1], x[i + 1]], [S[i] - (x[i + 1] - x[i]), S[i + 1]], color=BLUE, lw=1, alpha=0.5)
ax.axhline(0, color=INK2, lw=0.8)
dentro = [i for i, z in enumerate(zs) if 0 <= z["t_rel"] <= a0["trecho_de_7_zeros"] + 1e-9]
ax.scatter([x[i] for i in range(len(x))], [-2.6] * len(x), marker="|", s=160,
           color=[ORANGE if i in dentro else GRAY for i in range(len(x))], linewidth=2)
par = a0["par_mais_proximo"]
ip = [i for i, z in enumerate(zs) if z["indice"] == par[0]][0]
ax.annotate(f"par {par[0] % 1000000}/{par[1] % 1000000}: s = {br(a0['s'], '.3f')}, λ = {br(a0['lambda_colisao'], '.1e')}"
            "\n(o mais fácil de empurrar ao quarteto, §28)",
            (x[ip], -2.6), xytext=(-10, 22), textcoords="offset points", fontsize=8, color=INK,
            arrowprops={"arrowstyle": "-", "color": INK2, "lw": 0.7})
ax.set_ylim(-3.0, 2.6)
ax.set_xlabel(f"t − {a0['t_inicial'][:20].replace('.', ',')} (em espaçamentos médios, ⟨δ⟩ = {br(d, '.4f')})")
ax.set_ylabel("S(t)")
ax.set_title(f"(c) A aglomeração mais densa: 7 zeros em {br(a0['trecho_em_espacamentos'], '.2f')} espaçamentos")
ax.text(0.02, 0.95, "na aglomeração S sobe 1 por zero; entre zeros desce; todos os 7 na reta",
        transform=ax.transAxes, fontsize=8, color=INK2, va="top")

# (d) quão aglomerados os zeros podem ficar: contagem em 4 espaçamentos vs Poisson
ax = axs[1, 1]
dist = {int(k): v for k, v in ag["distribuicao_contagem_em_W"].items()}
n = sum(dist.values())
ks = list(range(0, 15))
obs = [dist.get(k, 0) for k in ks]
poi = [n * math.exp(-4) * 4 ** k / math.factorial(k) for k in ks]
w = 0.4
ax.bar([k - w / 2 for k in ks], [max(o, 0.5) for o in obs], width=w, color=BLUE, label="ζ, 2 054 383 janelas")
ax.bar([k + w / 2 for k in ks], poi, width=w, color=GRAY, label="pontos ao acaso (Poisson)")
ax.set_yscale("log")
ax.set_ylim(0.8, 3e6)
ax.set_xticks(ks)
ax.set_xlabel("zeros numa janela de 4 espaçamentos médios")
ax.set_ylabel("número de janelas")
ax.set_title("(d) Aglomerações são limitadas: no máximo 7 zeros")
ax.text(0.98, 0.70, "ao acaso, 5,1% das janelas teriam 8 ou mais;\nζ não tem nenhuma", transform=ax.transAxes,
        ha="right", fontsize=8, color=INK2)
ax.legend(loc="upper right")
ax.annotate("71 janelas com 7", (7 - w / 2, 71), xytext=(0, 40), textcoords="offset points", fontsize=8,
            color=INK, ha="center", arrowprops={"arrowstyle": "-", "color": INK2, "lw": 0.7})

fig.suptitle("Zeros fora da reta crítica: onde existem, onde ζ chega mais perto e como os zeros se aglomeram",
             x=0.06, ha="left", fontsize=13, fontweight="bold")
fig.savefig("aglomeracoes_e_fora_da_reta.png", dpi=150, bbox_inches="tight")
print("ok")
