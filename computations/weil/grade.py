"""A forma de Weil em funções-degrau: a matriz é de Toeplitz e os zeros aproximados ficam exatamente na reta.

    python3 grade.py      (grava grade.json)

A forma de Weil é invariante por translação (depende só de h = g ⋆ g̃). Restrita às funções-degrau numa grade uniforme
de passo δ em [−L, L] (N células), a sua matriz na base das células é de Toeplitz:

    τ(m) = ⟨D, Λ(· − mδ)⟩,   Λ(x) = max(δ − |x|, 0)   (a autocorrelação de uma célula),

com ⟨D, k⟩ = ∫ k(x)·2cosh(x/2) dx − log π·k(0) + A(k) − Σ_n Λ(n) n^{−1/2} [k(log n) + k(−log n)] e
A(k) = ∫_0^∞ [k(0)e^{−2x}/x − (k(x) + k(−x)) e^{−x/2}/(1 − e^{−2x})] dx. O termo do polo tem forma fechada:
∫ Λ(x − mδ)·2cosh(x/2) dx = 16·cosh(mδ/2)·(cosh(δ/2) − 1).

O teorema do kernel (`Toeplitz.zeros_no_circulo`) diz que, se o menor autovalor de T é simples, o polinômio
P(z) = Σ ξ_j z^j do autovetor tem todos os zeros no círculo unitário. A transformada do degrau é
ĝ(r) = δ·φ(irδ)·e^{−irL}·P(e^{irδ}), com φ(z) = (e^z − 1)/z, e então os zeros de ĝ são reais: r_k = arg(z_k)/δ.
`Grade.simples_de_queda` dá a simplicidade a partir da queda estrita do menor autovalor quando a grade ganha uma célula.

Mede-se, para cada (L, N): μ₁ = λ_min(T)/δ (a forma por ‖g‖²), a queda μ₁(N) < μ₁(N − 1), max | |z_k| − 1 |, a paridade
do autovetor, e os zeros r_k contra os γ_k.
"""
import json
import math

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.linalg import eigh
from scipy.special import exp1

from weil import GAMMAS, mangoldt_ate

SURF, INK, INK2, GRID = "#fcfcfb", "#0b0b0b", "#52514e", "#e4e3df"
CORES = ["#2a78d6", "#eb6834", "#6250d6", "#1baf7a", "#a3a29c", "#c4407a"]
plt.rcParams.update({
    "figure.facecolor": SURF, "axes.facecolor": SURF, "savefig.facecolor": SURF, "axes.edgecolor": GRID,
    "axes.labelcolor": INK2, "xtick.color": INK2, "ytick.color": INK2, "text.color": INK, "axes.grid": True,
    "grid.color": GRID, "grid.linewidth": 0.6, "axes.spines.top": False, "axes.spines.right": False,
    "font.size": 9.5, "axes.titlesize": 10.5, "axes.titleweight": "bold", "axes.titlelocation": "left",
    "legend.frameon": False, "legend.fontsize": 8.5,
})

XG, WG = leggauss(40)


def gauss(f, a, b):
    x = 0.5 * (b - a) * XG + 0.5 * (b + a)
    return 0.5 * (b - a) * np.sum(WG * f(x))


def simbolo(L, N):
    """τ(0..N−1) para a grade de passo δ = 2L/N em [−L, L]."""
    d = 2 * L / N
    lam = mangoldt_ate(max(int(math.floor(math.exp(2 * L))), 2))
    tau = np.zeros(N)
    peso = lambda x: np.exp(-x / 2) / (-np.expm1(-2 * x))
    for m in range(N):
        polo = 16 * math.cosh(m * d / 2) * (math.cosh(d / 2) - 1)
        if m == 0:
            arch = gauss(lambda x: d * np.exp(-2 * x) / x - 2 * (d - x) * peso(x), 0, d) + d * exp1(2 * d)
            k0 = d
        else:
            tri = lambda x: d - np.abs(x - m * d)
            arch = -gauss(lambda x: tri(x) * peso(x), (m - 1) * d, m * d) - gauss(lambda x: tri(x) * peso(x), m * d, (m + 1) * d)
            k0 = 0.0
        primos = 0.0
        for n in range(2, len(lam)):
            if lam[n]:
                t = math.log(n)
                kk = max(d - abs(t - m * d), 0.0) + (max(d - abs(-t - m * d), 0.0))
                primos += lam[n] / math.sqrt(n) * kk
        tau[m] = polo - math.log(math.pi) * k0 + arch - primos
    return tau, d


def bspline_c(p, d):
    """O B-spline centrado de ordem 2p (nós −pδ..pδ), normalizado como na partição da unidade."""
    from scipy.interpolate import BSpline
    return BSpline.basis_element(np.arange(-p, p + 1) * d, extrapolate=False)


def simbolo_spline(L, N, p):
    """Base φ_j = N_p(x − jδ) (B-splines de ordem p, grau p − 1) em [0, 2L], j = 0..N − p. A autocorrelação de N_p é
    k = δ·N_{2p}^c; devolve τ(m) = ⟨D, k(· − mδ)⟩ e a Gram G(m) = k(mδ)."""
    d = 2 * L / N
    M = N - p + 1
    B = bspline_c(p, d)
    k = lambda x: d * np.nan_to_num(B(np.asarray(x, dtype=float)))
    lam = mangoldt_ate(max(int(math.floor(math.exp(2 * L))), 2))
    peso = lambda x: np.exp(-x / 2) / (-np.expm1(-2 * x))
    lap = d ** (2 - 2 * p) * (4 * math.sinh(d / 4)) ** (2 * p)        # ∫ k(x)e^{±x/2} dx
    tau, G = np.zeros(M), np.zeros(M)
    for m in range(M):
        km0 = float(k(m * d))
        G[m] = km0
        polo = 2 * math.cosh(m * d / 2) * lap
        f = lambda x: km0 * np.exp(-2 * x) / x - (k(x - m * d) + k(x + m * d)) * peso(x)
        arch = sum(gauss(f, i * d, (i + 1) * d) for i in range(m + p)) + km0 * exp1(2 * (m + p) * d)
        primos = 0.0
        for n in range(2, len(lam)):
            if lam[n]:
                t = math.log(n)
                primos += lam[n] / math.sqrt(n) * float(k(t - m * d) + k(t + m * d))
        tau[m] = polo - math.log(math.pi) * km0 + arch - primos
    return tau, G, d


def analisa(L, N, p=1):
    if p == 1:
        tau, d = simbolo(L, N)
        G = np.zeros(N)
        G[0] = d
    else:
        tau, G, d = simbolo_spline(L, N, p)
    M = len(tau)
    T = np.array([[tau[abs(i - j)] for j in range(M)] for i in range(M)])
    Gm = np.array([[G[abs(i - j)] for j in range(M)] for i in range(M)])
    w, V = eigh(T, Gm)
    xi = V[:, 0]
    w_menor = eigh(T[:-1, :-1], Gm[:-1, :-1], eigvals_only=True, subset_by_index=[0, 0])[0]
    w = w * d
    w_menor = w_menor * d
    raizes = np.roots(xi[::-1])
    desvio = float(np.max(np.abs(np.abs(raizes) - 1)))
    r = np.sort(np.angle(raizes) / d)
    r = r[r > 0.05]
    pares = []
    for g in GAMMAS:
        if len(r):
            z = r[np.argmin(np.abs(r - g))]
            pares.append([g, float(z), float(z - g)])
    paridade = "par" if np.allclose(xi, xi[::-1], atol=1e-8) else ("ímpar" if np.allclose(xi, -xi[::-1], atol=1e-8) else "?")
    return {"L": L, "N": N, "p": p, "passo": d, "mu1": float(w[0] / d), "mu2": float(w[1] / d),
            "mu1_secao": float(w_menor / d), "queda_estrita": bool(w[0] < w_menor),
            "desvio_do_circulo": desvio, "paridade": paridade, "zeros_positivos": [float(x) for x in r[:40]],
            "comparacao": pares[:10]}


def main():
    res = []
    for p in (1, 2, 4):
      for L in (0.6, 0.8, 1.0, 1.2825):
        for N in (40, 80, 160, 320):
            a = analisa(L, N, p)
            res.append(a)
            print(f"p={p} L={L} N={N} δ={a['passo']:.4f}: μ₁={a['mu1']:.4e} μ₂={a['mu2']:.4e} seção={a['mu1_secao']:.4e} "
                  f"queda={a['queda_estrita']} desvio |z|−1={a['desvio_do_circulo']:.1e} {a['paridade']}  "
                  f"erros={[('%.1e' % e) for _, _, e in a['comparacao'][:5]]}", flush=True)
    json.dump(res, open("grade.json", "w"), indent=1)


if __name__ == "__main__":
    main()
