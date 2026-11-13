"""Desigualdade de Weil finita na escala log 4: só entram os primos 2 e 3.

Teste g = h ∗ h̃, com h(x) = bump suave de suporte [−log 2, log 2] (modulado por e^{iγx}); g tem suporte [−log 4, log 4].
Fórmula explícita (Guinand–Weil), com ĝ(t) = ∫ g(x) e^{itx} dx e zeros ρ = 1/2 + iγ_ρ:

    Σ_ρ ĝ(γ_ρ) = ĝ(i/2) + ĝ(−i/2) − Σ_n Λ(n)/√n · (g(log n) + g(−log n)) + (1/2π) ∫ ĝ(t) (Re ψ(1/4 + it/2) − log π) dt

Os dois lados são calculados independentemente (zeros de um lado; polo, primos 2 e 3 e termo arquimediano do outro).
Uso: python3 weil_finito.py [pasta com zeta_dp.py]
"""
import math
import sys

import numpy as np
from scipy.special import psi

sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else '.')
from zeta_dp import Z  # noqa: E402

A = math.log(2)  # suporte de h
X = np.linspace(-A, A, 4001)[1:-1]
DX = X[1] - X[0]
H = np.exp(-1.0 / (1.0 - (X / A) ** 2))


def h_hat(z, gam=0.0):
    """ĥ_γ(z) = ∫ h(x) e^{iγx} e^{izx} dx (z complexo)."""
    return np.sum(H * np.exp(1j * (z + gam) * X)) * DX


def g_hat(z, gam=0.0):
    """ĝ(z) = ĥ_γ(z) · conj(ĥ_γ(conj z)), a transformada de g = h_γ ∗ h̃_γ."""
    return h_hat(z, gam) * np.conj(h_hat(np.conj(z), gam))


def g_val(x, gam=0.0):
    """g(x) = ∫ h_γ(y) conj(h_γ(y − x)) dy."""
    Y = X
    hy = np.exp(-1.0 / (1.0 - (Y / A) ** 2)) * np.exp(1j * gam * Y)
    yx = Y - x
    ok = np.abs(yx) < A
    hyx = np.zeros_like(Y, dtype=complex)
    hyx[ok] = np.exp(-1.0 / (1.0 - (yx[ok] / A) ** 2)) * np.exp(1j * gam * yx[ok])
    return np.sum(hy * np.conj(hyx)) * DX


# zeros de ζ na reta até T, por troca de sinal de Z(t) e bisseção
def zeros_ate(T, passo=0.02):
    ts = np.arange(10.0, T, passo)
    zs = np.array([Z(t) for t in ts])
    out = []
    for i in np.nonzero(np.sign(zs[:-1]) * np.sign(zs[1:]) < 0)[0]:
        a, b = ts[i], ts[i + 1]
        fa = zs[i]
        for _ in range(50):
            m = 0.5 * (a + b)
            fm = Z(m)
            if np.sign(fm) == np.sign(fa):
                a, fa = m, fm
            else:
                b = m
        out.append(0.5 * (a + b))
    return np.array(out)


TMAX = 300.0
GAMMAS = zeros_ate(TMAX)
TT = np.linspace(-400, 400, 160001)
DT = TT[1] - TT[0]
ARQ = (psi(0.25 + 0.5j * TT).real - math.log(math.pi)) / (2 * math.pi)


def lados(gam=0.0):
    zeros = sum(g_hat(gm, gam) + g_hat(-gm, gam) for gm in GAMMAS).real
    polo = (g_hat(0.5j, gam) + g_hat(-0.5j, gam)).real
    p2 = (math.log(2) / math.sqrt(2) * (g_val(math.log(2), gam) + g_val(-math.log(2), gam))).real
    p3 = (math.log(3) / math.sqrt(3) * (g_val(math.log(3), gam) + g_val(-math.log(3), gam))).real
    ghat_t = np.array([g_hat(t, gam) for t in TT[::20]]).real
    arq = np.sum(ghat_t * ARQ[::20]) * DT * 20
    return zeros, polo, p2, p3, arq


print(f'zeros na reta até T = {TMAX:.0f}: {len(GAMMAS)} (esperado 138 até 300)')
z0, polo, p2, p3, arq = lados(0.0)
direita = polo - p2 - p3 + arq
print(f'γ = 0:  zeros = {z0:.10f}')
print(f'        polo {polo:.10f} − primo 2 {p2:.10f} − primo 3 {p3:.10f} + arquimediano {arq:.10f} = {direita:.10f}')
print(f'        diferença = {abs(z0 - direita):.2e}')
print()
print('γ      W = lado dos zeros    polo         −(2 + 3)      arquimediano   folga W/polo')
minW = None
for gam in [0, 5, 10, 14.13, 20, 30, 40, 50]:
    z0, polo, p2, p3, arq = lados(gam)
    d = polo - p2 - p3 + arq
    minW = z0 if minW is None else min(minW, z0)
    print(f'{gam:5.2f}  {z0: .6e} ({abs(z0 - d):.0e})  {polo: .4e}  {-(p2 + p3): .4e}  {arq: .4e}   {z0 / polo: .3e}')
print(f'\nmenor W na grade: {minW:.6e} (> 0)')
