"""Confere, por um caminho independente, o vale mais fundo de cada altura: as fases t*·log p mod 2π calculadas direto
em t* = 10^k + u* (Decimal, expoente + 60 dígitos, π por Machin com outra precisão) em vez de fase(10^k) + u*·log p.
"""
import json
import math
import sys
from decimal import Decimal, getcontext
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from euler import pi_decimal, primos  # noqa: E402

R = Path(__file__).resolve().parent / "resultados"
g = json.loads((R / "varredura_euler.json").read_text())
out = {}
P = primos(100000)
for chave, r in g.items():
    k = int(chave[2:])
    v = r["euler"]["vales"][0]
    dig = k + 60
    dpi = 2 * pi_decimal(dig + 7)
    getcontext().prec = dig + 15
    t = Decimal(10) ** k + Decimal(repr(v["u"]))
    soma = 0.0
    for q in P:
        ph = float((t * Decimal(int(q)).ln()) % dpi)
        soma += -math.log(abs(1 - q ** -0.5 * complex(math.cos(ph), -math.sin(ph))))
    out[chave] = {"u": v["u"], "log_P_varredura": v["log_P"], "log_P_direto": soma, "diferenca": soma - v["log_P"]}
    print(chave, out[chave], flush=True)
(R / "confere.json").write_text(json.dumps(out, indent=1))
