"""ζ(s) por Euler–Maclaurin em complex128 (numpy, vetorizado). Não certificado: só para medir e comparar.

ζ(s) ≈ Σ_{n<N} n^{−s} + N^{1−s}/(s−1) + N^{−s}/2 + Σ_{k=1}^{M} B_{2k}/(2k)! (s)_{2k−1} N^{−s−2k+1}.
Com N = 30, M = 12 e |s| ≈ 15 o erro de truncamento é < 10⁻¹³ (o termo seguinte, conferido em `erro_em`).
"""
from fractions import Fraction as F
import math

import numpy as np

B2K = [F(1, 6), F(-1, 30), F(1, 42), F(-1, 30), F(5, 66), F(-691, 2730), F(7, 6), F(-3617, 510),
       F(43867, 798), F(-174611, 330), F(854513, 138), F(-236364091, 2730), F(8553103, 6)]
COEF = [float(B2K[k - 1] / math.factorial(2 * k)) for k in range(1, len(B2K) + 1)]


def zeta(s, N=30, M=12):
    s = np.asarray(s, dtype=complex)
    n = np.arange(1, N, dtype=float)
    tot = np.exp(-np.multiply.outer(s, np.log(n))).sum(axis=-1)
    lN = math.log(N)
    tot = tot + np.exp((1 - s) * lN) / (s - 1) + 0.5 * np.exp(-s * lN)
    poch = s.copy()                       # (s)_1
    pot = np.exp(-(s + 1) * lN)           # N^{−s−1}
    for k in range(1, M + 1):
        tot = tot + COEF[k - 1] * poch * pot
        poch = poch * (s + 2 * k - 1) * (s + 2 * k)
        pot = pot / (N * N)
    return tot


def erro_em(s, N=30, M=12):
    """Módulo do primeiro termo omitido (estimativa do erro de truncamento)."""
    s = complex(s)
    poch = s
    for j in range(1, 2 * M + 1):
        poch *= s + j
    return abs(COEF[M] * poch * N ** (-(s.real + 2 * M + 1)))


def deriv(f, z, k, r=0.05, m=64):
    """f^{(k)}(z) pela fórmula de Cauchy (trapézio em |w − z| = r, m nós): erro ~ (r/dist ao polo)^m."""
    th = 2 * np.pi * np.arange(m) / m
    w = z + r * np.exp(1j * th)
    return math.factorial(k) / (r ** k) * np.mean(f(w) * np.exp(-1j * k * th))
