"""A máquina de teste da RH (critério de Lagarias na forma Π₁ usada por Yedidia–Aaronson 2016):

    RH  ⟺  para todo n ≥ 1:  (H_{δ(n)} − n²/2)² < 36 n³,
    δ(n) = ∏_{m<n} ∏_{j≤m} η(j) = ∏_{m<n} lcm(1, …, m),   H_N = Σ_{k≤N} 1/k.

A máquina procura um n que viole a desigualdade; ela para ⟺ a RH é falsa. Aqui ela roda em ponto flutuante (não
certificado) até N = 10⁷: log δ(n) = Σ_{m<n} ψ(m), e para N enorme H_N = log N + γ + 1/(2N) + O(N⁻²), com erro abaixo
da precisão. A razão r(n) = (H_{δ(n)} − n²/2)²/(36n³) teria que passar de 1 para a máquina parar.

    python3 maquina_rh.py > maquina_rh.json
"""
import json
import math

import numpy as np

N = 10_000_000
EULER = 0.5772156649015329
# Λ(n) por crivo
lam = np.zeros(N + 1)
crivo = np.ones(N + 1, bool)
crivo[:2] = False
for p in range(2, int(N ** 0.5) + 1):
    if crivo[p]:
        crivo[p * p::p] = False
primos = np.nonzero(crivo)[0]
for p in primos:
    lp = math.log(p)
    q = p
    while q <= N:
        lam[q] = lp
        q *= p
psi = np.cumsum(lam)                    # ψ(m)
soma_psi = np.concatenate([[0.0], np.cumsum(psi)])[:N + 1]   # Σ_{m<n} ψ(m) = log δ(n)
n = np.arange(N + 1, dtype=float)
D = soma_psi + EULER - n * n / 2        # H_{δ(n)} − n²/2 (n ≥ 5: δ(n) ≥ 144, correção 1/(2δ) desprezível)
r = np.zeros(N + 1)
r[1:] = D[1:] ** 2 / (36 * n[1:] ** 3)
# pequenos n: exato
from fractions import Fraction
def delta(k):
    d = 1
    for m in range(k):
        l = 1
        for j in range(1, m + 1):
            l = l * j // math.gcd(l, j)
        d *= l
    return d
exatos = []
for k in range(1, 8):
    dk = delta(k)
    H = sum(Fraction(1, i) for i in range(1, dk + 1)) if dk <= 10 ** 6 else None
    val = (H - Fraction(k * k, 2)) ** 2 if H is not None else None
    exatos.append({"n": k, "delta": dk, "H_delta": float(H) if H is not None else None,
                   "razao": float(val / (36 * k ** 3)) if val is not None else None})
    r[k] = exatos[-1]["razao"] if exatos[-1]["razao"] is not None else r[k]
amostra = [int(x) for x in np.unique(np.round(np.logspace(0, 7, 400)).astype(int))]
print(json.dumps({"N": N, "max_razao": float(r[1:].max()), "n_do_max": int(r[1:].argmax() + 1),
                  "max_razao_n_maior_que_1000": float(r[1000:].max()), "parou": bool((r[1:] >= 1).any()),
                  "exatos": exatos, "amostra": [{"n": k, "r": float(r[k]), "D": float(D[k])} for k in amostra]},
                 ensure_ascii=False))
