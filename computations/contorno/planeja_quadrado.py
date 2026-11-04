"""Planeja as peças que certificam max |ζ| ≤ U no bordo do quadrado [1/10, 9/10] × [a, b] (a = 1373/100, b = 727/50),
que contém o disco |s − z₀| ≤ 2/5. Cada peça é um `ret` fino em volta de um trecho de lado, com centros na própria
aresta, e é aceita pelo kernel se |ζ(c)| + (B/r)·h ≤ U em todos os centros (`peca_sup`), com B = cotaQ na região de
Cauchy [s0 − r, s1 + r] × [a − r, b + r].

    python3 planeja_quadrado.py U   (imprime as peças e o custo; grava pecas_quadrado_U.json)

Custo medido de uma avaliação no kernel (N = 12, M = 8, 32 bits): σ com denominador 10: ~0,6 s; 40: ~1,4 s;
400: ~6,6 s. Por isso os centros das arestas horizontais ficam em σ = k/D com D ≤ 400 (o menor que passa) e
os das verticais em σ = 1/10 e 9/10 exatos.
"""
import json
import math
import sys
from fractions import Fraction as Fr

import numpy as np

from contornos import cotaQ
from zeta_em import zeta

S0, S1 = Fr(1, 10), Fr(9, 10)
A, B_ = Fr(1373, 100), Fr(727, 50)
FOLGA = 0.004          # margem para o raio do retângulo certificado e arredondamentos
HFINO = Fr(1, 10000)   # meia largura dos retângulos finos


def cota_regiao(s0, s1, a, b, r):
    """Melhor cotaQ (N ≤ 12, M ≤ 10) com R² ≥ (s1 + r)² + (b + r)², d ≤ a − r."""
    R = Fr(math.ceil(math.hypot(float(s1 + r), float(b + r)) * 100) + 1, 100)
    d = a - r
    best = None
    for N in range(3, 13):
        for M in range(2, 11):
            v = cotaQ(N, M, R, d)
            if best is None or v < best[0]:
                best = (v, N, M)
    B = Fr(math.ceil(float(best[0]) * 1000) + 1, 1000)
    return B, best[1], best[2], R, d


def vertical(sig, a, b, U, r):
    """Aresta Re = sig, Im em [a, b]: ret [sig − HFINO, sig + HFINO] × [a, b], centros (sig, a + ht(2j+1))."""
    s0, s1 = sig - HFINO, sig + HFINO
    Bc, Nc, Mc, R, d = cota_regiao(s0, s1, a, b, r)
    L = float(Bc / r)
    for n in range(1, 4000):
        ht = (b - a) / (2 * n)
        h = math.sqrt(float(HFINO) ** 2 + float(ht) ** 2)
        cs = np.array([complex(float(sig), float(a + ht * (2 * j + 1))) for j in range(n)])
        v = np.abs(zeta(cs))
        if v.max() + FOLGA + L * h * 1.0001 <= U:
            return {"tipo": "v", "s0": str(s0), "s1": str(s1), "a": str(a), "b": str(b), "r": str(r), "B": str(Bc),
                    "Nc": Nc, "Mc": Mc, "R": str(R), "d": str(d), "hs": str(HFINO), "ht": str(ht), "ns": 1, "nt": n,
                    "max_centro": float(v.max()), "L": L, "custo_den": 10}
    return None


def horizontal(tim, s0, s1, U, r):
    """Aresta Im = tim, Re em [s0, s1]: ret [s0, s1] × [tim − HFINO, tim + HFINO], centros σ = s0 + (2i+1)/D
    (hs = 1/D), com D o menor de 20, 40, 100, 200, 400 que passa: σ fica com denominador D."""
    a, b = tim - HFINO, tim + HFINO
    Bc, Nc, Mc, R, d = cota_regiao(s0, s1, a, b, r)
    L = float(Bc / r)
    for D in (20, 40, 100, 200, 400):
        hs = Fr(1, D)
        n = (s1 - s0) / (2 * hs)
        if n.denominator != 1:
            continue
        n = int(n)
        h = math.sqrt(float(hs) ** 2 + float(HFINO) ** 2)
        cs = np.array([complex(float(s0 + hs * (2 * i + 1)), float(tim)) for i in range(n)])
        v = np.abs(zeta(cs))
        if v.max() + FOLGA + L * h * 1.0001 <= U:
            dmax = max((s0 + hs * (2 * i + 1)).denominator for i in range(n))
            return {"tipo": "h", "s0": str(s0), "s1": str(s1), "a": str(a), "b": str(b), "r": str(r), "B": str(Bc),
                    "Nc": Nc, "Mc": Mc, "R": str(R), "d": str(d), "hs": str(hs), "ht": str(HFINO), "ns": n, "nt": 1,
                    "max_centro": float(v.max()), "L": L, "custo_den": dmax}
    return None


def custo_s(den):
    return 0.55 if den <= 10 else 0.8 if den <= 20 else 1.0 if den <= 40 else 1.3 if den <= 100 else 2.2 if den <= 200 else 6.6


def plano(U):
    pecas = []
    # aresta esquerda (Re = 1/10): r < 1/10 − HFINO
    rl = Fr(99, 1000) - HFINO
    passos = [A + Fr(k, 10) for k in range(0, 9)] + [B_]
    passos = sorted(set(p for p in passos if A <= p <= B_))
    for x, y in zip(passos, passos[1:]):
        pecas.append(vertical(S0, x, y, U, rl))
    # aresta direita (Re = 9/10)
    for x, y in zip(passos, passos[1:]):
        pecas.append(vertical(S1, x, y, U, Fr(2, 5)))
    # arestas horizontais: trechos [1/10, 3/10] (r < 1/10), [3/10, 6/10] (r < 3/10), [6/10, 9/10] (r < 6/10 → 2/5)
    for tim in (A, B_):
        for (x, y, r) in ((S0, Fr(1, 5), rl), (Fr(1, 5), Fr(3, 10), Fr(19, 100)),
                          (Fr(3, 10), Fr(3, 5), Fr(29, 100)), (Fr(3, 5), S1, Fr(2, 5))):
            pecas.append(horizontal(tim, x, y, U, r))
    if any(p is None for p in pecas):
        return None
    n = sum(p["ns"] * p["nt"] for p in pecas)
    t = sum(p["ns"] * p["nt"] * custo_s(p["custo_den"]) for p in pecas)
    return pecas, n, t


def raio(U, rho=0.4):
    alvo = 0.783297 / 2 - 0.0023
    lo, hi = 0.0, rho
    for _ in range(100):
        m = (lo + hi) / 2
        if 4 * U / (rho - m) ** 2 * (m + 1e-5) <= alvo:
            lo = m
        else:
            hi = m
    return lo


if __name__ == "__main__":
    for U in [float(x) for x in sys.argv[1:]] or [0.7, 0.8, 1.0, 1.2]:
        p = plano(U)
        if p is None:
            print(U, "sem plano")
            continue
        pecas, n, t = p
        print(f"U = {U}: {len(pecas)} peças, {n} avaliações, ~{t / 60:.1f} min no kernel, raio de unicidade ≈ {raio(U):.4f}")
        json.dump(pecas, open(f"pecas_quadrado_{U}.json", "w"), indent=1)
