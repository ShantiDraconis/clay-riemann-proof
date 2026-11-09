"""O limite de (C): os estados fundamentais de Weil convergem para Ξ?

    python3 limite.py      (lê alta_<L>.json e base_<L>_n<n>.json; grava limite.json e limite.png; ~10 min)

Para cada escala, com os coeficientes de alta precisão do estado fundamental g*_L (base cos(πjx/L)):

(a) No lado de Fourier: E_L(r) = [ĝ*_L(r)/Ξ(r)] / [ĝ*_L(0)/Ξ(0)], com Ξ(r) = ξ(½ + ir). Se E_L → 1 em compactos, os
    estados fundamentais normalizados convergem para Ξ. A conta mostra ln E_L(r) ≈ c(L)·r² (o quociente é quase uma
    gaussiana) e mede c(L) = ln E_L(10)/100, mais o desvio |E_L/e^{c r²} − 1| em pontos complexos.
(b) No espaço x: g*_L contra o núcleo de Riemann–Pólya Φ (Ξ(r) = ∫ Φ(u) e^{iru} du), por mínimos quadrados
    g* ≈ αΦ + βΦ'' em [0, L). Pelo item (a), −β/α deve ser ≈ c(L) (porque e^{cr²}Ξ ↔ Φ − cΦ'' + …).

Para cada L usa a maior base disponível. Isto é medida numérica; não prova (C).
"""
import glob
import json

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mpmath as mp

mp.mp.dps = 60

SURF, INK, INK2, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#e4e3df"
CORES = ["#2a78d6", "#eb6834", "#6250d6", "#1baf7a", "#a3a29c", "#c4407a", "#b08a1e", "#3a9fb5", "#7a5c3e"]
plt.rcParams.update({
    "figure.facecolor": SURF, "axes.facecolor": SURF, "savefig.facecolor": SURF, "axes.edgecolor": GRID,
    "axes.labelcolor": INK2, "xtick.color": INK2, "ytick.color": INK2, "text.color": INK, "axes.grid": True,
    "grid.color": GRID, "grid.linewidth": 0.6, "axes.spines.top": False, "axes.spines.right": False,
    "font.size": 9.5, "axes.titlesize": 10.5, "axes.titleweight": "bold", "axes.titlelocation": "left",
    "legend.frameon": False, "legend.fontsize": 8.5,
})


def carrega(f):
    r = json.load(open(f))
    L = mp.mpf(r["L"])
    c = [mp.mpf(x) for x in r["coeficientes"]]
    a = [mp.pi * j / L for j in range(len(c))]
    return r["L"], r["n"], L, c, a


def ghat(c, a, L, z):
    s = mp.mpf(0)
    for cj, aj in zip(c, a):
        for k in (z - aj, z + aj):
            s += cj * (L if abs(k) < mp.mpf(10) ** (-40) else mp.sin(k * L) / k)
    return s


def Xi(r):
    s = mp.mpf(1) / 2 + 1j * r
    return s * (s - 1) / 2 * mp.pi ** (-s / 2) * mp.gamma(s / 2) * mp.zeta(s)


def Phi(u, d=0):
    f = lambda v: mp.nsum(lambda n: (2 * mp.pi ** 2 * n ** 4 * mp.exp(9 * v / 2) - 3 * mp.pi * n ** 2 * mp.exp(5 * v / 2))
                          * mp.exp(-mp.pi * n ** 2 * mp.exp(2 * v)), [1, mp.inf])
    return f(u) if d == 0 else mp.diff(f, u, d)


def escolhe_arquivos():
    melhor = {}
    for f in glob.glob("alta_[0-9]*.json") + glob.glob("base_*.json"):
        r = json.load(open(f))
        if "coeficientes" not in r:
            continue
        if r["L"] not in melhor or r["n"] > melhor[r["L"]][1]:
            melhor[r["L"]] = (f, r["n"])
    return [melhor[L][0] for L in sorted(melhor)]


def main():
    X0 = Xi(0)
    rs = [mp.mpf(k) / 2 for k in range(1, 81)]                     # 0,5 .. 40
    complexos = [mp.mpc(0, 2), mp.mpc(0, 4), mp.mpc(10, 3), mp.mpc(25, 5)]
    linhas = []
    for f in escolhe_arquivos():
        Lf, n, L, c, a = carrega(f)
        g0 = ghat(c, a, L, 0)
        E = lambda z: (ghat(c, a, L, z) / Xi(z)) / (g0 / X0)
        lnE = [float(mp.re(mp.log(E(r)))) for r in rs]
        cL = lnE[19] / 100                                         # r = 10
        desvio = [float(abs(E(z) / mp.exp(cL * z ** 2) - 1)) for z in complexos]
        # espaço x
        gx = lambda x: sum(cj * mp.cos(aj * x) for cj, aj in zip(c, a))
        xs = [L * k / 20 for k in range(20)]
        G = [gx(x) for x in xs]
        P = [Phi(x) for x in xs]
        P2 = [Phi(x, 2) for x in xs]
        A = mp.matrix([[p, q] for p, q in zip(P, P2)])
        sol = mp.lu_solve(A.T * A, A.T * mp.matrix(G))
        al, be = sol[0], sol[1]
        escala = max(abs(x) for x in G)
        res_phi = max(abs(gi - (G[0] / P[0]) * p) for gi, p in zip(G, P)) / escala
        res_phi2 = max(abs(gi - al * p - be * q) for gi, p, q in zip(G, P, P2)) / escala
        linhas.append({"L": Lf, "n": n, "arquivo": f, "c_L": cL, "c_L_vezes_e2L": cL * float(mp.exp(2 * L)),
                       "lnE_sobre_r2_em_r": {str(float(r)): v / float(r) ** 2 for r, v in zip(rs, lnE) if r in (2, 5, 10, 20, 30, 40)},
                       "desvio_complexo": dict(zip(["2i", "4i", "10+3i", "25+5i"], desvio)),
                       "menos_beta_sobre_alfa": float(-be / al), "residuo_x_so_Phi": float(res_phi),
                       "residuo_x_Phi_menos_cPhi2": float(res_phi2), "g_borda_sobre_g0": float(gx(L) / G[0]),
                       "curva_lnE": lnE,
                       "x": [float(x) for x in xs], "g_norm": [float(gi / G[0]) for gi in G],
                       "Phi_norm": [float(p / P[0]) for p in P]})
        t = linhas[-1]
        print(f"L={Lf:<7} n={n:<3} c(L)={cL:.6f}  c·e^(2L)={t['c_L_vezes_e2L']:.5f}  −β/α={t['menos_beta_sobre_alfa']:.6f}  "
              f"desvio complexo={['%.1e' % d for d in desvio]}  resíduo x: Φ {res_phi:.4f}, Φ−cΦ'' {res_phi2:.5f}", flush=True)
    json.dump({"r": [float(r) for r in rs], "escalas": linhas}, open("limite.json", "w"), indent=1)
    figura(linhas, rs)


def figura(linhas, rs):
    fig, ax = plt.subplots(1, 3, figsize=(16, 4.8))
    a = ax[0]
    r2 = [float(r) ** 2 for r in rs]
    for i, t in enumerate(linhas):
        a.plot(r2, t["curva_lnE"], lw=1.6, color=CORES[i % len(CORES)], label=f"L = {t['L']}")
    a.set_xlabel("r²   (em L = 0,6 os picos ficam nos zeros de Ξ ainda não capturados, γ > 25)")
    a.set_ylabel("ln E_L(r)")
    a.set_title("(a) ĝ*_L/Ξ normalizado: ln E_L ≈ c(L)·r²")
    a.legend(loc="upper left", ncol=2, fontsize=8)
    b = ax[1]
    Ls = [t["L"] for t in linhas]
    b.semilogy(Ls, [t["c_L"] for t in linhas], "o-", color=CORES[0], ms=5, lw=1.6, label="c(L) (lado de Fourier)")
    b.semilogy(Ls, [t["menos_beta_sobre_alfa"] for t in linhas], "s", color=CORES[1], ms=5, mfc="none",
               label="−β/α (espaço x, g* ≈ αΦ + βΦ'')")
    ref = linhas[0]["c_L"] * mp.exp(2 * linhas[0]["L"])
    b.semilogy(Ls, [float(ref * mp.exp(-2 * L)) for L in Ls], "--", color=INK2, lw=1, label="∝ e^{−2L}")
    b.set_xlabel("L")
    b.set_ylabel("c(L)")
    b.set_title("(b) c(L) → 0 (quase como e^{−2L})")
    b.legend(loc="lower left", fontsize=8)
    d = ax[2]
    longe = max(linhas, key=lambda t: t["L"])
    d.plot(longe["x"], longe["Phi_norm"], "-", lw=1.6, color=INK, label="Φ (núcleo de Riemann–Pólya)")
    for i, t in enumerate(linhas):
        if t["L"] in (0.6, 1.0, 1.5):
            d.plot(t["x"], t["g_norm"], "o", ms=4, color=CORES[i % len(CORES)], label=f"g*_L, L = {t['L']}")
    d.set_xlabel("x")
    d.set_ylabel("normalizado em x = 0")
    d.set_title("(c) No espaço x, g*_L se aproxima de Φ")
    d.legend(loc="upper right", fontsize=8)
    fig.tight_layout()
    fig.savefig("limite.png", dpi=150)


if __name__ == "__main__":
    import sys
    if sys.argv[1:] == ["--figura"]:
        d = json.load(open("limite.json"))
        figura(d["escalas"], d["r"])
    else:
        main()
