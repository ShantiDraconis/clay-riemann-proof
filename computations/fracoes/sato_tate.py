"""BSD no cotidiano das frações: a distribuição de x_p = a_p/(2√p) ∈ [−1, 1] (a RH local de cada fator de L(E, s)).

    python3 sato_tate.py > sato_tate.json

E₀: y² = x³ − x (multiplicação complexa): a_p = 0 para p ≡ 3 (mod 4) (fração supersingular → ½, Deuring) e os
outros com densidade 1/(π√(1 − x²)). E₁: y² = x³ − 2 também tem CM (por Z[ω]): a_p = 0 para p ≡ 2 (mod 3).
E₂: y² = x³ + x + 1 (sem CM): Sato–Tate, densidade (2/π)√(1 − x²) (teorema de Barnet-Lamb–Geraghty–Harris–Taylor 2011).
Primos de boa redução até 2·10⁵.
"""
import json
import math

import numpy as np

X = 200_000
crivo = np.ones(X + 1, bool)
crivo[:2] = False
for p in range(2, int(X ** 0.5) + 1):
    if crivo[p]:
        crivo[p * p::p] = False
primos = [int(p) for p in np.nonzero(crivo)[0] if p >= 5]
CURVAS = {"E0: y² = x³ − x": (-1, 0, 4 * (-1) ** 3), "E1: y² = x³ − 2": (0, -2, 27 * 4),
          "E2: y² = x³ + x + 1": (1, 1, 4 + 27)}
saida = {}
for nome, (a, b, disc) in CURVAS.items():
    xs = []
    zeros = 0
    for p in primos:
        if disc % p == 0:
            continue
        x = np.arange(p, dtype=np.int64)
        f = (x * x % p * x + a * x + b) % p
        quad = np.zeros(p, bool)
        quad[(x * x) % p] = True
        Np = 1 + int(np.where(f == 0, 1, np.where(quad[f], 2, 0)).sum())
        ap = p + 1 - Np
        zeros += ap == 0
        xs.append(ap / (2 * math.sqrt(p)))
    xs = np.array(xs)
    h, borda = np.histogram(xs, bins=40, range=(-1, 1))
    saida[nome] = {"primos": len(xs), "fracao_a_p_zero": zeros / len(xs), "max_abs_x": float(np.abs(xs).max()),
                   "momentos": {"m2": float((xs ** 2).mean()), "m4": float((xs ** 4).mean())},
                   "histograma": h.tolist(), "bordas": borda.tolist()}
print(json.dumps({"X": X, "curvas": saida}, ensure_ascii=False))
