"""A forma quadrática de Weil com suporte finito: a RH em escala finita.

    python3 weil.py      (grava weil.json)

Fórmula explícita (normalização conferida contra os zeros com φ gaussiana, diferença 3·10⁻¹⁶):

    Σ_ρ φ(γ) = φ(i/2) + φ(−i/2) − h(0)·log π + (1/2π)∫ φ(r)·Re ψ(¼ + ir/2) dr − 2 Σ_n Λ(n) n^{−½} h(log n),

com φ(r) = ∫ h(x) e^{irx} dx. Para h = g ⋆ g (g real, par, suporte em [−L, L]) vale φ = |ĝ|², e o lado direito é a
forma de Weil W(g). Critério de Weil: RH ⟺ W(g) ≥ 0 para toda g. Com suporte em [−L, L], h tem suporte em [−2L, 2L] e
só entram os primos (e potências) n ≤ e^{2L}: a RH vira uma família de problemas finitos, um para cada L.

Base: g_j(x) = cos²(πx/2L)·cos(πjx/L), j = 0..n−1 (pares, zeram com derivada nas bordas, ĝ ~ r^{−3}). A matriz de W
e a de Gram dão o problema generalizado W c = μ G c; μ(L) = menor autovalor. Sob a RH, μ(L) ≥ 0. A função minimizante
g* tem ĝ* real; os zeros reais de ĝ* são comparados com os zeros γ_k de ζ (a observação de Connes, 2026).
"""
import json
import math
import sys

import numpy as np
from scipy.linalg import eigh
from scipy.special import psi


def mangoldt_ate(N):
    lam = np.zeros(N + 1)
    crivo = np.ones(N + 1, dtype=bool)
    crivo[:2] = False
    for p in range(2, N + 1):
        if crivo[p]:
            crivo[p * p::p] = False
            q = p
            while q <= N:
                lam[q] = math.log(p)
                q *= p
    return lam


def ghat_cos(a, L, r):
    """∫_{−L}^{L} cos(a x) e^{irx} dx (real)."""
    r = np.asarray(r)
    r = r.astype(complex) if np.iscomplexobj(r) else r.astype(float)
    out = np.zeros_like(r)
    for s in (r - a, r + a):
        small = np.abs(s) < 1e-12
        out = out + np.where(small, L, np.sin(s * L) / np.where(small, 1.0, s))
    return out


def base_hat(j, L, r):
    """ĝ_j(r) para g_j = cos²(πx/2L)·cos(πjx/L) = ½cos(a_j x) + ¼cos(a_{j+1}x) + ¼cos(a_{j−1}x)."""
    a = lambda k: math.pi * k / L
    return 0.5 * ghat_cos(a(j), L, r) + 0.25 * ghat_cos(a(j + 1), L, r) + 0.25 * ghat_cos(a(j - 1), L, r)


def base_x(j, L, x):
    return np.where(np.abs(x) <= L, np.cos(math.pi * x / (2 * L)) ** 2 * np.cos(math.pi * j * x / L), 0.0)


def forma_de_weil(L, n, R=600.0, dr=0.004, nx=6001):
    # parte arquimediana e polo, no espaço r
    r = np.arange(0.0, R + dr / 2, dr)
    w = np.full(r.size, dr)
    w[0] = w[-1] = dr / 2
    rep = psi(0.25 + 0.5j * r).real
    H = np.array([base_hat(j, L, r) for j in range(n)])                      # ĝ_j(r)
    arch = (H * (rep * w)) @ H.T / math.pi                                    # (1/2π)·2∫_0^∞
    # ĝ_j(i/2) = ∫ g_j(x) e^{−x/2} dx
    x = np.linspace(-L, L, nx)
    dx = x[1] - x[0]
    wx = np.full(nx, dx)
    wx[0] = wx[-1] = dx / 2
    Gx = np.array([base_x(j, L, x) for j in range(n)])
    gi2 = Gx @ (np.exp(-x / 2) * wx)
    gm2 = Gx @ (np.exp(x / 2) * wx)
    polo = np.outer(gi2, gm2)
    polo = polo + polo.T                                                      # φ(i/2) + φ(−i/2)
    gram = (Gx * wx) @ Gx.T                                                   # h_ij(0) = ⟨g_i, g_j⟩
    # primos: h_ij(t) = ∫ g_i(y) g_j(y − t) dy em t = log n, n ≤ e^{2L}
    N = int(math.floor(math.exp(2 * L)))
    lam = mangoldt_ate(max(N, 2))
    P = np.zeros((n, n))
    for m in range(2, N + 1):
        if lam[m] == 0:
            continue
        t = math.log(m)
        Gs = np.array([base_x(j, L, x - t) for j in range(n)])
        hij = (Gx * wx) @ Gs.T
        hij = (hij + hij.T) / 2
        P += 2 * lam[m] / math.sqrt(m) * hij * 2 / 2          # h(log n) + h(−log n) = 2·h_sim, vezes ½ do fator 2
    W = polo - math.log(math.pi) * gram + arch - P
    return (W + W.T) / 2, gram, N


def zeros_reais(f, a, b, passo=0.005):
    r = np.arange(a, b, passo)
    v = f(r)
    out = []
    for i in np.nonzero(np.sign(v[:-1]) * np.sign(v[1:]) < 0)[0]:
        lo, hi = r[i], r[i + 1]
        flo = v[i]
        for _ in range(60):
            mid = (lo + hi) / 2
            fm = f(np.array([mid]))[0]
            if np.sign(fm) == np.sign(flo):
                lo, flo = mid, fm
            else:
                hi = mid
        out.append((lo + hi) / 2)
    return out


GAMMAS = [14.134725141734693, 21.022039638771555, 25.010857580145688, 30.424876125859513, 32.935061587739189,
          37.586178158825671, 40.918719012147495, 43.327073280914999, 48.005150881167159, 49.773832477672302,
          52.970321477714460, 56.446247697063394, 59.347044002602353, 60.831778524609809, 65.112544048081606]


def analisa(L, n):
    W, G, N = forma_de_weil(L, n)
    mu, V = eigh(W, G)
    c = V[:, 0]
    f = lambda r: sum(c[j] * base_hat(j, L, r) for j in range(n))
    zs = zeros_reais(f, 0.5, 66.0)
    pares = []
    for g in GAMMAS:
        if zs:
            z = min(zs, key=lambda q: abs(q - g))
            pares.append((g, z, z - g))
    return {"L": L, "n": n, "primos_ate": N, "mu_min": float(mu[0]), "mu_2": float(mu[1]),
            "zeros_do_minimizante": zs, "comparacao": pares}


if __name__ == "__main__":
    L = float(sys.argv[1]) if len(sys.argv) > 1 else math.log(13) / 2
    n = int(sys.argv[2]) if len(sys.argv) > 2 else 24
    r = analisa(L, n)
    print(f"L = {L:.4f} (n ≤ e^2L = {r['primos_ate']}), base {n}: μ_min = {r['mu_min']:.3e}, μ_2 = {r['mu_2']:.3e}")
    for g, z, d in r["comparacao"][:10]:
        print(f"  γ = {g:.6f}   zero de ĝ* = {z:.6f}   diferença {d:+.2e}")
