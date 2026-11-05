"""A cascata dos autovalores de Weil, os zeros do estado fundamental e a sua realidade.

    python3 cascata.py      (grava weil.json e weil.png; alguns minutos)

(a) μ_k(L), k = 1..5, para L de 0,2 a 1,0 (em precisão dupla; abaixo de ~10⁻¹² é ruído).
(b) Em L = ½·log 13 (primos até 13), o erro |zero de ĝ* − γ_k| para os zeros de ζ até a altura 66.
(c) Contagem de zeros do estado fundamental: princípio do argumento no retângulo [0,3; 60] × [−1,5; 1,5] contra as
    trocas de sinal na reta real.
"""
import json
import math

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from scipy.linalg import eigh

from weil import GAMMAS, analisa, base_hat, forma_de_weil

SURF, INK, INK2, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#e4e3df"
CORES = ["#2a78d6", "#eb6834", "#6250d6", "#1baf7a", "#a3a29c"]
plt.rcParams.update({
    "figure.facecolor": SURF, "axes.facecolor": SURF, "savefig.facecolor": SURF, "axes.edgecolor": GRID,
    "axes.labelcolor": INK2, "xtick.color": INK2, "ytick.color": INK2, "text.color": INK, "axes.grid": True,
    "grid.color": GRID, "grid.linewidth": 0.6, "axes.spines.top": False, "axes.spines.right": False,
    "font.size": 9.5, "axes.titlesize": 10.5, "axes.titleweight": "bold", "axes.titlelocation": "left",
    "legend.frameon": False, "legend.fontsize": 8.5,
})


def conta_zeros(L, n, T=60.0, h=1.5):
    W, G, N = forma_de_weil(L, n)
    mu, V = eigh(W, G)
    c = V[:, 0]
    f = lambda z: sum(c[j] * base_hat(j, L, z) for j in range(n))
    a, b, m = 0.3, T, 60000
    lados = [np.linspace(a - 1j * h, b - 1j * h, m), np.linspace(b - 1j * h, b + 1j * h, m),
             np.linspace(b + 1j * h, a + 1j * h, m), np.linspace(a + 1j * h, a - 1j * h, m)]
    voltas = sum(np.sum(np.angle(f(l)[1:] / f(l)[:-1])) for l in lados) / (2 * math.pi)
    r = np.linspace(a, b, 200001)
    v = f(r).real
    return {"L": L, "n": n, "primos_ate": N, "zeros_no_retangulo": round(float(voltas), 3),
            "trocas_de_sinal_reais": int(np.sum(np.sign(v[:-1]) * np.sign(v[1:]) < 0))}


def main():
    Ls = np.round(np.arange(0.2, 1.01, 0.05), 3)
    tabela = []
    for L in Ls:
        W, G, N = forma_de_weil(float(L), 16)
        mu = eigh(W, G, eigvals_only=True)
        tabela.append({"L": float(L), "primos_ate": N, "mu": [float(x) for x in mu[:5]]})
    conn = analisa(math.log(13) / 2, 24)
    contagens = [conta_zeros(L, n) for L, n in ((0.6, 16), (0.9, 20), (math.log(13) / 2, 24), (1.5, 28))]
    out = {"tabela_mu": tabela, "connes_primos_ate_13": conn, "contagens": contagens, "piso_de_ruido": 1e-12}
    json.dump(out, open("weil.json", "w"), indent=1)

    fig, ax = plt.subplots(1, 2, figsize=(13, 5))
    a = ax[0]
    for k in range(5):
        xs = [t["L"] for t in tabela if t["mu"][k] > 1e-12]
        ys = [t["mu"][k] for t in tabela if t["mu"][k] > 1e-12]
        a.semilogy(xs, ys, "o-", ms=4, lw=1.6, color=CORES[k], label=f"μ_{k + 1}")
    a.axhline(1e-12, color=INK2, lw=0.9, ls="--")
    a.text(0.21, 2e-12, "piso de ruído (precisão dupla)", fontsize=8, color=INK2)
    a.set_xlabel("L (suporte [−L, L]; entram os primos até e^{2L})")
    a.set_ylabel("autovalor da forma de Weil")
    a.set_title("(a) A cascata: cada autovalor despenca numa escala")
    a.legend(loc="upper right", ncol=5, fontsize=8)
    b = ax[1]
    comp = conn["comparacao"]
    ks = np.arange(1, len(comp) + 1)
    err = [max(abs(d), 1e-16) for _, _, d in comp]
    b.semilogy(ks, err, "o-", ms=6, lw=1.6, color=CORES[0])
    b.set_xticks(ks)
    b.set_xlabel("k (k-ésimo zero de ζ)")
    b.set_ylabel("|zero de ĝ* − γ_k|")
    b.set_title("(b) Só com os primos até 13: os zeros do minimizante são os de ζ")
    b.axhline(1e-12, color=INK2, lw=0.9, ls="--")
    fig.tight_layout()
    fig.savefig("weil.png", dpi=150)
    for t in tabela:
        print(t["L"], t["primos_ate"], ["%.2e" % x for x in t["mu"]])
    for c in contagens:
        print(c)


if __name__ == "__main__":
    main()
