"""Figura: a máquina de teste da RH rodando até n = 10⁷ e a ponte com BSD.

    python3 figura.py      (lê maquina_rh.json e bsd_produto.json; grava maquina_e_bsd.png)

(a) r(n) = (H_{δ(n)} − n²/2)²/(36 n³): a máquina para (RH falsa) só se r(n) ≥ 1. Ponto flutuante, não certificado;
    os seis primeiros n são contas exatas (e conferidas no kernel, Maquina.lag_ate_6).
(b) Produto parcial de Birch e Swinnerton-Dyer Π_{p≤X} N_p/p contra log X: posto 0 fica limitado, posto 1 cresce
    como C·log X. Cada fator local satisfaz a RH local a_p² ≤ 4p (kernel até p = 97, aqui até 10⁵).
"""
import json

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
M = json.load(open("maquina_rh.json"))
B = json.load(open("bsd_produto.json"))
fig, ax = plt.subplots(1, 2, figsize=(12, 4.4))
a = ax[0]
am = [x for x in M["amostra"] if x["r"] > 0]
a.loglog([x["n"] for x in am], [x["r"] for x in am], color=CORES[1], lw=1.6, label="r(n), ponto flutuante")
a.loglog([x["n"] for x in M["exatos"][:6]], [x["razao"] for x in M["exatos"][:6]], "o", ms=6, color=CORES[0],
         mec=SURF, mew=1.2, label="n = 1…6, exato (kernel)")
a.axhline(1, color=CORES[4], lw=1.5, ls="--")
a.text(2, 1.4, "r = 1: a máquina para (RH falsa)", color=INK, fontsize=8.5)
a.set_ylim(1e-10, 10)
a.set_xlabel("n")
a.set_ylabel("r(n) = (H_δ(n) − n²/2)² / (36 n³)")
a.set_title("(a) A máquina de teste da RH até n = 10⁷: não parou")
a.legend(loc="lower left")
b = ax[1]
for (nome, v), cor in zip(B["curvas"].items(), (CORES[0], CORES[3])):
    b.plot([x["log_X"] for x in v["amostra"]], [x["produto"] for x in v["amostra"]], color=cor, lw=2,
           label=nome + (" (posto 0)" if "x³ − x" in nome else " (posto 1)"))
b.set_xlabel("log X")
b.set_ylabel("Π_{p ≤ X} N_p / p")
b.set_title("(b) BSD: o produto cresce como (log X)^posto")
b.legend(loc="upper left")
fig.tight_layout()
fig.savefig("maquina_e_bsd.png", dpi=150)
print("ok")
