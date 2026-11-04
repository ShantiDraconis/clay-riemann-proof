"""O critério de Lagarias conferido para todo n ≤ N: σ(n) ≤ H_n + e^{H_n}·log H_n.

    python3 lagarias.py [N]      (padrão N = 10^7)

Lagarias (2002, Amer. Math. Monthly 109, 534–543), a partir de Robin (1984): RH ⟺ a desigualdade vale para todo
n ≥ 1 (igualdade só em n = 1). Cada n é uma conta finita: σ(n) é inteiro (crivo exato) e H_n é racional.

Conferência em duas etapas: float64 para todos os n (σ exato; H_n por soma acumulada, erro relativo < 10⁻¹²), e os
n com folga relativa abaixo de 10⁻⁶, mais os 30 de menor folga, de novo com Fraction exata para H_n e Decimal de 60
dígitos (exp e ln do Decimal são corretamente arredondados). Grava resultados/lagarias.json.

Isto NÃO prova RH: confere uma quantidade finita de n. RH é a afirmação para todo n.
"""
import json
import sys
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path

import numpy as np

N = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 7
AQUI = Path(__file__).resolve().parent

sigma = np.zeros(N + 1, dtype=np.int64)
for d in range(1, N + 1):
    sigma[d::d] += d
n = np.arange(1, N + 1, dtype=np.float64)
H = np.cumsum(1.0 / n)
rhs = H + np.exp(H) * np.log(H)
s = sigma[1:].astype(np.float64)
folga = (rhs - s) / rhs  # folga relativa
falhas_float = np.nonzero(folga[1:] <= 0)[0] + 2  # n ≥ 2

getcontext().prec = 60


def confere_exato(m: int) -> float:
    Hm = sum(Fraction(1, k) for k in range(1, m + 1))
    Hd = Decimal(Hm.numerator) / Decimal(Hm.denominator)
    r = Hd + Hd.exp() * Hd.ln()
    return float((r - Decimal(int(sigma[m]))) / r)


ordem = np.argsort(folga[1:])[:30] + 2
suspeitos = sorted(set(int(x) for x in ordem) | set(int(x) for x in (np.nonzero(folga[1:] < 1e-6)[0] + 2)))
exatos = {m: confere_exato(m) for m in suspeitos if m <= 200000}
res = {
    "N": N,
    "n_1": "igualdade (σ(1) = 1 = H_1 + e·log 1)",
    "falhas_float64_n_ge_2": [int(x) for x in falhas_float],
    "folga_minima_n_ge_2": {"n": int(ordem[0]), "folga_relativa": float(folga[ordem[0] - 1]),
                            "sigma": int(sigma[ordem[0]]), "H_n": float(H[ordem[0] - 1])},
    "menores_folgas": [{"n": int(m), "sigma": int(sigma[m]), "folga_relativa_float64": float(folga[m - 1]),
                        "folga_relativa_exata": exatos.get(int(m))} for m in ordem],
    "todos_conferidos": len(falhas_float) == 0 and all(v > 0 for v in exatos.values()),
}
(AQUI / "resultados").mkdir(exist_ok=True)
(AQUI / "resultados" / "lagarias.json").write_text(json.dumps(res, ensure_ascii=False, indent=1))
print(json.dumps({k: v for k, v in res.items() if k != "menores_folgas"}, ensure_ascii=False, indent=1))
print([(x["n"], round(x["folga_relativa_float64"], 6)) for x in res["menores_folgas"][:12]])
