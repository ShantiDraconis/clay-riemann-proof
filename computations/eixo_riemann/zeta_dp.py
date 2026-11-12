"""ζ(s) em precisão dupla, independente do analisador de Borwein.

Euler–Maclaurin para Re s >= 0, equação funcional para Re s < 0, derivadas pela fórmula de Cauchy
(regra do trapézio no círculo, convergência geométrica). Precisão típica 1e-12 para |t| <= 10^4.
"""
import cmath
import math
from fractions import Fraction

import numpy as np

# B_2 .. B_32
_B = [Fraction(1, 6), Fraction(-1, 30), Fraction(1, 42), Fraction(-1, 30), Fraction(5, 66),
      Fraction(-691, 2730), Fraction(7, 6), Fraction(-3617, 510), Fraction(43867, 798),
      Fraction(-174611, 330), Fraction(854513, 138), Fraction(-236364091, 2730),
      Fraction(8553103, 6), Fraction(-23749461029, 870), Fraction(8615841276005, 14322),
      Fraction(-7709321041217, 510)]
_COEF = [float(b / math.factorial(2 * (k + 1))) for k, b in enumerate(_B)]


def _zeta_em(s, m=12):
    N = int(math.ceil(4 * (abs(s) + 2 * m) / (2 * math.pi))) + 10
    n = np.arange(1, N, dtype=float)
    soma = complex(np.sum(np.exp(-s * np.log(n))))
    Nf = float(N)
    soma += Nf ** (1 - s) / (s - 1) + 0.5 * Nf ** (-s)
    fator = s * Nf ** (-s - 1)          # s(s+1)...(s+2k-2) N^{-s-2k+1}, k = 1
    for k in range(m):
        soma += _COEF[k] * fator
        fator *= (s + 2 * k + 1) * (s + 2 * k + 2) / (Nf * Nf)
    return soma


def loggamma(z):
    """log Γ(z) (algum ramo; serve para exp e para módulo)."""
    desloc = 0j
    while z.real < 12:
        desloc -= cmath.log(z)
        z += 1
    r = (z - 0.5) * cmath.log(z) - z + 0.5 * math.log(2 * math.pi)
    zz = z
    for k, b in enumerate(_B[:10]):
        r += float(b) / ((2 * k + 2) * (2 * k + 1) * zz)
        zz *= z * z
    return r + desloc


def zeta(s):
    s = complex(s)
    if s.real >= 0:
        return _zeta_em(s)
    # ζ(s) = 2^s π^{s-1} sin(πs/2) Γ(1-s) ζ(1-s)
    return (2 ** s) * (math.pi ** (s - 1)) * cmath.sin(math.pi * s / 2) * cmath.exp(loggamma(1 - s)) * _zeta_em(1 - s)


def derivadas(s, kmax=3, r=0.25, M=64):
    """[ζ(s), ζ'(s), ..., ζ^(kmax)(s)] pela fórmula integral de Cauchy."""
    s = complex(s)
    w = [cmath.exp(2j * math.pi * j / M) for j in range(M)]
    v = [zeta(s + r * wj) for wj in w]
    out = []
    for k in range(kmax + 1):
        a = sum(vj * wj ** (-k) for vj, wj in zip(v, w)) / M
        out.append(a * math.factorial(k) / r ** k)
    out[0] = zeta(s)
    return out


def theta(t):
    """θ de Riemann–Siegel (série assintótica, t >= 10)."""
    return t / 2 * math.log(t / (2 * math.pi)) - t / 2 - math.pi / 8 + 1 / (48 * t) + 7 / (5760 * t ** 3)


def Z(t):
    return (cmath.exp(1j * theta(t)) * zeta(0.5 + 1j * t)).real
