"""A força mínima que tira um par de zeros da reta, em cada par frágil e em cada nó (estimativa, fora do kernel).

    python3 forca_rs.py SAIDA.json LISTA1.csv.gz [LISTA2.csv.gz ...]
    FORCA_PARES=pares.json python3 forca_rs.py ...   (também os pares que começam nesses índices: nós, aglomerado)

Na reta, ζ(½ + it) = e^{−iθ(t)} Z(t) com Z real. Entre dois zeros vizinhos γ₁ < γ₂, Z tem uma "lombada" de altura
Z* = Z(t*) (t* o extremo, ≈ o ponto médio quando o par é apertado). Uma perturbação que preserve a equação funcional
e a realidade de Z na reta (Z ↦ Z − ε·sinal(Z*)) só tira os dois zeros da reta quando ε passa de |Z*|:

    ε < |Z*|: dois zeros reais (na reta);  ε = |Z*|: zero duplo;  ε > |Z*|: o par ½ ± b + it*, b ≈ √(2(ε − |Z*|)/|Z''|),

e, com a conjugação, o quarteto ½ ± b ± it*. É a lei da raiz quadrada (ClayRiemannProof/Colisao.lean,
ClayRiemannProof/Forca.lean) com o empurrão vertical no lugar do tempo do calor. No modelo quadrático
Z ≈ (Z''/2)(t − γ₁)(t − γ₂), Z'' = −8Z*/Δ², e o tempo do fluxo de de Bruijn que faz o mesmo é Δ_x²/8 (x = 2γ).

Z(t) pela fórmula de Riemann–Siegel com o primeiro termo de correção: Z = 2 Σ_{n ≤ N} n^{−½} cos(θ(t) − t log n)
+ (−1)^{N−1} (t/2π)^{−¼} C₀(p), N = ⌊√(t/2π)⌋, p = frac(√(t/2π)); erro O(t^{−3/4}) (≈ 3·10⁻⁹ em 3·10¹²). As fases
t log n são reduzidas mod 2π com 60 dígitos (t = T₀ + τ, T₀ log n exato, τ log n em ponto flutuante). Conferência:
|Z| nos próprios zeros da lista tem de ficar no nível do erro (é a coluna "Z nos zeros").

Fora do kernel; estimativa em ponto flutuante, não bola certificada (a versão certificada é forca.c, com a Arb).
"""
import gzip
import json
import math
import sys
from decimal import Decimal, getcontext

import numpy as np

getcontext().prec = 60
SAI, LISTAS = sys.argv[1], sys.argv[2:]
PI = Decimal("3.14159265358979323846264338327950288419716939937510582097494459230781640628620899")
DOISPI = 2 * PI


def theta(t):
    return (t / 2) * (t / (2 * PI)).ln() - t / 2 - PI / 8 + 1 / (48 * t) + Decimal(7) / (5760 * t ** 3)


# zeros
idx, gam = [], []
for p in LISTAS:
    for ln in gzip.open(p, "rt"):
        if ln[0].isdigit():
            a = ln.strip().split(",")
            idx.append(int(a[0]))
            gam.append(Decimal(a[1]))
ordem = sorted(range(len(idx)), key=lambda i: idx[i])
idx = [idx[i] for i in ordem]
gam = [gam[i] for i in ordem]
uniq = {}
for i, g in zip(idx, gam):
    uniq[i] = g
idx = sorted(uniq)
gam = [uniq[i] for i in idx]
n = len(idx)
T0 = int(gam[0])
Tmax = float(gam[-1])
NMAX = int(math.sqrt(Tmax / (2 * math.pi))) + 2
print(f"{n} zeros, T0 = {T0}, N até {NMAX}", flush=True)

# log n com 60 dígitos pelos primos (log de composto = soma), e T0·log n mod 2π
crivo = np.ones(NMAX + 1, dtype=bool)
crivo[:2] = False
for q in range(2, int(NMAX ** 0.5) + 1):
    if crivo[q]:
        crivo[q * q::q] = False
primos = np.nonzero(crivo)[0]
logp = {int(q): Decimal(int(q)).ln() for q in primos}
menor = np.zeros(NMAX + 1, dtype=np.int64)  # menor fator primo
for q in primos[::-1]:
    menor[q::q] = q
logD = [Decimal(0)] * (NMAX + 1)
for m in range(2, NMAX + 1):
    q = int(menor[m])
    logD[m] = logD[m // q] + logp[q]
fase0 = np.array([float((T0 * logD[m]) % DOISPI) for m in range(1, NMAX + 1)])
logf = np.array([float(logD[m]) for m in range(1, NMAX + 1)])
amp = 1 / np.sqrt(np.arange(1, NMAX + 1, dtype=np.float64))
print("fases prontas", flush=True)


def Z(t):
    """Z(t), t Decimal."""
    tf = float(t)
    a = math.sqrt(tf / (2 * math.pi))
    N = int(a)
    p = a - N
    tau = float(t - T0)
    th = float(theta(t) % DOISPI)
    fase = th - fase0[:N] - tau * logf[:N]
    s = 2 * float(np.dot(amp[:N], np.cos(fase)))
    c0 = math.cos(2 * math.pi * (p * p - p - 1 / 16)) / math.cos(2 * math.pi * p)
    return s + (-1) ** (N - 1) * (tf / (2 * math.pi)) ** -0.25 * c0


rho = lambda t: math.log(t / (2 * math.pi)) / (2 * math.pi)  # noqa: E731
gaps = [(float(gam[i + 1] - gam[i]), i) for i in range(n - 1)]
gaps.sort()
alvo = [i for _, i in gaps[:300]]
import os  # noqa: E402
if os.environ.get("FORCA_PARES"):
    pos = {k: i for i, k in enumerate(idx)}
    extra = [pos[k] for k in json.load(open(os.environ["FORCA_PARES"])) if k in pos and pos[k] + 1 < n]
    alvo = list(dict.fromkeys(alvo + extra))
pares = []
for i in alvo:
    g1, g2 = gam[i], gam[i + 1]
    D = g2 - g1
    m = (g1 + g2) / 2
    zm = Z(m)
    # extremo: parábola por três pontos
    h = D / 4
    za, zb = Z(m - h), Z(m + h)
    den = za - 2 * zm + zb
    desl = float(h) * (za - zb) / (2 * den) if den != 0 else 0.0
    ze = Z(m + Decimal(desl)) if abs(desl) < float(h) else zm
    z1, z2 = Z(g1), Z(g2)
    Df = float(D)
    zpp = -8 * abs(ze) / Df ** 2 * (1 if ze > 0 else -1)
    T = float(m)
    pares.append({
        "indice": idx[i], "gamma_1": str(g1), "gamma_2": str(g2), "intervalo": Df, "s": Df * rho(T),
        "Z_estrela": ze, "forca": abs(ze), "forca_relativa": abs(ze) / math.sqrt(math.log(T / (2 * math.pi))),
        "Z_nos_zeros": max(abs(z1), abs(z2)), "Zpp_modelo": zpp,
        "tempo_do_calor": (2 * Df) ** 2 / 8,
        "b_com_epsilon_2forca": math.sqrt(2 * abs(ze) / abs(zpp)) if zpp else None,
    })
pares.sort(key=lambda r: r["forca"])
ruido = max(r["Z_nos_zeros"] for r in pares)
out = {"zeros": n, "faixa": [str(gam[0]), str(gam[-1])], "metodo": "Riemann–Siegel + C0, fases com 60 dígitos",
       "ruido_Z_nos_zeros_max": ruido, "pares": pares}
json.dump(out, open(SAI, "w"), ensure_ascii=False, indent=1)
for r in pares[:25]:
    print(f"{r['indice']} t={r['gamma_1'][:24]} Δ={r['intervalo']:.6f} s={r['s']:.4f} |Z*|={r['forca']:.3e} "
          f"rel={r['forca_relativa']:.2e} Z''={r['Zpp_modelo']:.3e} calor={r['tempo_do_calor']:.3e} "
          f"Z(zeros)={r['Z_nos_zeros']:.1e}")
print("ruído máximo de Z nos zeros:", ruido)
