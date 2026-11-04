"""A ponte RH–BSD: os fatores locais de L(E, s) satisfazem a RH local (Hasse, a_p² ≤ 4p), e o produto parcial de
Birch e Swinnerton-Dyer Π_{p≤X} N_p/p cresce como C·(log X)^r, r = posto.

    python3 bsd_produto.py > bsd_produto.json

E₀: y² = x³ − x (posto 0, condutor 32);  E₁: y² = x³ − 2 (posto 1, ponto (3, 5)). Primos de boa redução p ≥ 5.
N_p = #E(𝔽_p) = p + 1 − a_p, contado exatamente (numpy). Também a RH local de cada fator: a_p² ≤ 4p.
"""
import json
import math

import numpy as np

X = 100_000
crivo = np.ones(X + 1, bool)
crivo[:2] = False
for p in range(2, int(X ** 0.5) + 1):
    if crivo[p]:
        crivo[p * p::p] = False
primos = [int(p) for p in np.nonzero(crivo)[0] if p >= 5]
CURVAS = {"E0: y² = x³ − x": (-1, 0), "E1: y² = x³ − 2": (0, -2)}
saida = {}
for nome, (a, b) in CURVAS.items():
    logprod = 0.0
    serie, maxrazao, viol = [], 0.0, 0
    marcas = set(int(v) for v in np.unique(np.round(np.logspace(1, math.log10(X), 120)).astype(int)))
    for p in primos:
        x = np.arange(p, dtype=np.int64)
        f = (x * x % p * x + a * x + b) % p
        quad = np.zeros(p, bool)
        quad[(x * x) % p] = True
        ny = np.where(f == 0, 1, np.where(quad[f], 2, 0))
        Np = 1 + int(ny.sum())
        ap = p + 1 - Np
        maxrazao = max(maxrazao, ap * ap / (4 * p))
        viol += ap * ap > 4 * p
        logprod += math.log(Np / p)
        serie.append((p, logprod))
    pts = [(p, lp) for p, lp in serie if any(abs(p - m) <= 0 for m in [])]
    amostra = []
    alvo = sorted(marcas)
    j = 0
    for p, lp in serie:
        while j < len(alvo) and alvo[j] <= p:
            amostra.append({"X": p, "produto": math.exp(lp), "log_X": math.log(p)})
            j += 1
    saida[nome] = {"primos": len(primos), "max_ap2_sobre_4p": maxrazao, "violacoes_de_hasse": int(viol),
                   "produto_final": math.exp(serie[-1][1]), "amostra": amostra}
print(json.dumps({"X": X, "curvas": saida}, ensure_ascii=False))
