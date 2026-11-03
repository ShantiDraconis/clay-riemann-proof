"""Fator aritmético de ζ na reta: o produto de Euler truncado P_X(t) = Π_{p ≤ X} (1 − p^{−1/2−it})^{−1}.

Fases t·log p mod 2π com precisão arbitrária (Decimal): a altura t pode ter milhares de dígitos (10^1000). Para
pontos t₀ + u perto de uma base t₀, a fase é (t₀·log p mod 2π) + u·log p em ponto flutuante (u pequeno).
"""
import math
from decimal import Decimal, getcontext

import numpy as np


def primos(X):
    c = np.ones(X + 1, dtype=bool)
    c[:2] = False
    for q in range(2, int(X ** 0.5) + 1):
        if c[q]:
            c[q * q::q] = False
    return np.nonzero(c)[0]


def pi_decimal(dig):
    getcontext().prec = dig + 10
    # Machin: π = 16 atan(1/5) − 4 atan(1/239)
    def atan_inv(x):
        x = Decimal(x)
        x2, termo, soma, k = x * x, 1 / x, 1 / x, 1
        while True:
            termo /= -x2
            t = termo / (2 * k + 1)
            if abs(t) < Decimal(10) ** (-(dig + 5)):
                break
            soma += t
            k += 1
        return soma
    return 16 * atan_inv(5) - 4 * atan_inv(239)


class Fases:
    """log p e t₀·log p mod 2π para os primos p ≤ X, com `dig` dígitos (precisa de dig > log10(t₀) + 20)."""

    def __init__(self, t0, X, dig):
        getcontext().prec = dig + 10
        self.p = primos(X)
        self.t0 = Decimal(t0)
        dpi = 2 * pi_decimal(dig)
        getcontext().prec = dig + 10
        self.logp = np.array([float(Decimal(int(q)).ln()) for q in self.p])
        self.fase0 = np.array([float((self.t0 * Decimal(int(q)).ln()) % dpi) for q in self.p])
        self.amp = self.p.astype(float) ** -0.5

    def log_P(self, u, X=None):
        """log P_X(t₀ + u) (complexo) para um vetor u; X ≤ o X da construção."""
        k = len(self.p) if X is None else int(np.searchsorted(self.p, X, side="right"))
        u = np.atleast_1d(np.asarray(u, dtype=float))
        out = np.zeros(len(u), dtype=complex)
        for i in range(0, len(u), 4096):
            uu = u[i:i + 4096, None]
            ph = self.fase0[None, :k] + uu * self.logp[None, :k]
            z = self.amp[None, :k] * np.exp(-1j * ph)  # p^{−1/2−it}
            out[i:i + 4096] = -np.log(1 - z).sum(axis=1)
        return out
