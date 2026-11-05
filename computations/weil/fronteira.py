"""A fronteira do ataque de Weil em alta precisão: a lei de (B) e a altura capturada.

    python3 fronteira.py      (lê alta_<L>.json, grava fronteira.json e fronteira.png)

(a) −log₁₀ μ₁(L) e −log₁₀ |zero_k(L) − γ_k| para k = 1..5: os erros de (B) caem junto com μ₁ (a razão erro/μ₁ cresce
    devagar).
(b) O erro em cada zero, para cada escala: a frente de captura anda para cima com L.
(c) A altura capturada (o maior γ_k com todos os erros até ele abaixo de 10⁻⁵) contra 2πe^{2L}.
(d) A razão κ_k = |zero_k − γ_k|/μ₁: estável quando a base cresce (base_<L>_n<n>.json), embora μ₁ mude.

Os μ são cotas superiores de Rayleigh–Ritz (base finita) e não estão convergidos em n para L grande: em L = 1,5, μ₁ cai
de 3,4·10⁻⁷⁹ (n = 56) para 8,3·10⁻⁸⁴ (n = 64). A razão erro/μ₁ quase não muda (10 167 → 9 551). Por isso o C da lei de
Chuk só é calculado aqui como diagnóstico.
"""
import glob
import json
import math

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

SURF, INK, INK2, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#e4e3df"
CORES = ["#2a78d6", "#eb6834", "#6250d6", "#1baf7a", "#a3a29c", "#c4407a", "#b08a1e", "#3a9fb5", "#7a5c3e"]
plt.rcParams.update({
    "figure.facecolor": SURF, "axes.facecolor": SURF, "savefig.facecolor": SURF, "axes.edgecolor": GRID,
    "axes.labelcolor": INK2, "xtick.color": INK2, "ytick.color": INK2, "text.color": INK, "axes.grid": True,
    "grid.color": GRID, "grid.linewidth": 0.6, "axes.spines.top": False, "axes.spines.right": False,
    "font.size": 9.5, "axes.titlesize": 10.5, "axes.titleweight": "bold", "axes.titlelocation": "left",
    "legend.frameon": False, "legend.fontsize": 8.5,
})


def N_riemann(T):
    """Riemann–von Mangoldt: N(T) ≈ (T/2π)·log(T/2πe) + 7/8."""
    return T / (2 * math.pi) * math.log(T / (2 * math.pi * math.e)) + 7 / 8


def main():
    dados = []
    for f in glob.glob("alta_[0-9]*.json"):
        r = json.load(open(f))
        if r["L"] < 0.55:
            continue
        dados.append(r)
    dados.sort(key=lambda r: r["L"])
    linhas = []
    for r in dados:
        L = r["L"]
        mu1 = float(r["mu"][0])
        erros = [(g, abs(float(e))) for g, e in r["erro_por_zero"]]
        captura = 0.0
        for g, e in erros:
            if e < 1e-5:
                captura = g
            else:
                break
        Tst = 2 * math.pi * math.exp(2 * L)
        N = N_riemann(Tst)
        linhas.append({
            "L": L, "n": r["n"], "dps": r.get("dps"), "primos_ate": r["primos_ate"], "mu1": mu1,
            "menos_log10_mu1": -math.log10(mu1), "erro_1_a_5": [e for _, e in erros[:5]],
            "razao_erro1_mu1": erros[0][1] / mu1, "kappa_1_a_5": [e / mu1 for _, e in erros[:5]], "altura_capturada": captura, "T_estrela": Tst,
            "C_de_Chuk": -math.log(mu1) / (N / math.log(N)), "retangulo": r["retangulo"],
            "zeros_reais_ate_70": sum(1 for z in r["zeros_reais"] if 0.3 < float(z) < 70),
        })
    base = []
    for f in sorted(glob.glob("base_*.json")):
        r = json.load(open(f))
        mu1 = float(r["mu"][0])
        base.append({"L": r["L"], "n": r["n"], "mu1": mu1,
                     "kappa_1_a_5": [abs(float(e)) / mu1 for _, e in r["erro_por_zero"][:5]],
                     "retangulo": r["retangulo"]})
    json.dump({"escalas": linhas, "verificacao_da_base": base}, open("fronteira.json", "w"), indent=1)
    for b in base:
        print(f"base: L={b['L']} n={b['n']} μ₁={b['mu1']:.3e} κ₁..₅ = {['%.0f' % k for k in b['kappa_1_a_5']]}")
    for t in linhas:
        print(f"L={t['L']:<7} n={t['n']:<3} μ₁={t['mu1']:.3e}  erro₁/μ₁={t['razao_erro1_mu1']:8.0f}  "
              f"capturado até {t['altura_capturada']:6.2f} (2πe^2L = {t['T_estrela']:6.1f})  C={t['C_de_Chuk']:.2f}  "
              f"retângulo={t['retangulo']}")

    Ls = [t["L"] for t in linhas]
    fig, ax = plt.subplots(2, 2, figsize=(13, 9))
    a = ax[0][0]
    a.plot(Ls, [t["menos_log10_mu1"] for t in linhas], "o-", color=INK, lw=2, ms=5, label="μ₁ (autovalor)")
    for k in range(5):
        a.plot(Ls, [-math.log10(t["erro_1_a_5"][k]) for t in linhas], "o-", ms=4, lw=1.4, color=CORES[k],
               label=f"|zero_{k + 1} − γ_{k + 1}|")
    a.set_xlabel("L (suporte [−L, L])")
    a.set_ylabel("−log₁₀")
    a.set_title("(a) A lei de (B): os erros caem com o autovalor")
    a.legend(loc="upper left", fontsize=8)

    b = ax[0][1]
    for i, r in enumerate(dados):
        gs = [g for g, _ in r["erro_por_zero"]]
        es = [max(abs(float(e)), 1e-80) for _, e in r["erro_por_zero"]]
        b.semilogy(gs, es, "o-", ms=3, lw=1.2, color=CORES[i % len(CORES)], label=f"L = {r['L']}")
    b.axhline(1e-5, color=INK2, lw=0.9, ls="--")
    b.set_xlabel("γ_k (altura do zero de ζ)")
    b.set_ylabel("|zero de ĝ* − γ_k|")
    b.set_title("(b) A frente de captura sobe com L")
    b.legend(loc="lower right", ncol=3, fontsize=7.5)

    c = ax[1][0]
    c.plot(Ls, [t["T_estrela"] for t in linhas], "-", color=INK2, lw=1.4, label="2πe^{2L}")
    c.plot(Ls, [t["altura_capturada"] for t in linhas], "o", color=CORES[0], ms=6,
           label="maior γ com erros < 10⁻⁵ até ele (γ ≤ 70)")
    c.axhline(70, color=INK2, lw=0.9, ls="--")
    c.text(1.3, 72, "limite da conta (γ ≤ 70)", fontsize=8, color=INK2)
    c.set_xlabel("L")
    c.set_ylabel("altura")
    c.set_title("(c) A altura capturada contra 2πe^{2L}")
    c.legend(loc="upper left")

    d = ax[1][1]
    for k in range(5):
        d.semilogy(Ls, [t["kappa_1_a_5"][k] for t in linhas], "o-", ms=4, lw=1.4, color=CORES[k], label=f"κ_{k + 1}")
        d.semilogy([b["L"] for b in base], [b["kappa_1_a_5"][k] for b in base], "o", ms=9, mfc="none",
                   mec=CORES[k], mew=1.3)
    d.set_xlabel("L")
    d.set_ylabel("κ_k = |zero_k − γ_k| / μ₁")
    d.set_title("(d) Erro ≈ κ·μ₁; κ quase não muda com a base (círculos: base maior)")
    d.legend(loc="upper left", ncol=5, fontsize=8)
    fig.tight_layout()
    fig.savefig("fronteira.png", dpi=150)


if __name__ == "__main__":
    main()
