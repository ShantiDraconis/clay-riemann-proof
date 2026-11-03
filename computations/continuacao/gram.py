"""Lei de Gram, regra de Rosser e S(t) em toda a lista da continuação (fora do kernel).

    python3 gram.py faixas/ resultado/

Lê os zeros{I}.csv.gz contíguos (índices seguidos a partir de N(C0) + 1, C0 e N(C0) de inicio.json) e calcula, com
θ(t)/π = θ(C0)/π + θ'(C0)/π·h + θ''(C0)/(2π)·h² (h = t − C0 ≤ 5·10⁵; o termo seguinte é < 10⁻⁹):

* quantos intervalos de Gram [g_m, g_{m+1}) têm 0, 1, 2, 3, … zeros;
* a fração de pontos de Gram ruins (S(g_m) = N(g_m) − m − 1 ímpar);
* os blocos entre pontos de Gram bons em que o número de zeros difere do comprimento (exceções de Rosser);
* S(t) = N(t) − θ(t)/π − 1 logo antes e logo depois de cada zero: máximo e mínimo.

As leis usadas estão no kernel (Leis.lei_gram, Leis.rosser_bloco, Gram.S_gram, Gram.bloco_par); os números não.
"""
import gzip
import json
import math
import sys
from collections import Counter
from decimal import Decimal
from pathlib import Path

import numpy as np
from mpmath import mp, mpf, siegeltheta, pi, log, floor

mp.dps = 50
ENT, SAI = Path(sys.argv[1]), Path(sys.argv[2])
SAI.mkdir(parents=True, exist_ok=True)
INICIO = json.loads((Path(__file__).parent / "inicio.json").read_text())
C0, N0 = INICIO["C0"], int(INICIO["N(C0)"])
rows = []
for I in range(64):
    p = next(iter(ENT.rglob(f"zeros{I}.csv.gz")), None)
    if p is None:
        break
    rows += [l.strip().split(",") for l in gzip.open(p, "rt")][1:]
idx = np.array([int(r[0]) for r in rows], dtype=np.int64)
if not len(idx) or idx[0] != N0 + 1 or not np.all(np.diff(idx) == 1):
    (SAI / "gram.json").write_text(json.dumps({"erro": "lista não contígua a partir de N(C0) + 1"}) + "\n")
    sys.exit(0)
t0 = mpf(C0)
th0 = siegeltheta(t0) / pi
A = int(floor(th0))
B, C = float(log(t0 / (2 * pi)) / 2 / pi), float(1 / (4 * pi * t0))
h = np.array([float(Decimal(r[1]) - Decimal(C0)) for r in rows])
frac = float(th0 - A) + B * h + C * h * h
for k in (0, len(rows) // 2, len(rows) - 1):  # conferência com θ exato
    assert abs(float(siegeltheta(mpf(rows[k][1])) / pi - A) - frac[k]) < 1e-7
m = np.floor(frac).astype(np.int64) + A
S_dep = (idx - A) - frac - 1
cont = Counter(m.tolist())
m0, m1 = int(m.min()) + 1, int(m.max())
dist = Counter(cont.get(j, 0) for j in range(m0, m1))
js = np.arange(m0, m1 + 1)
Sg = N0 + np.searchsorted(np.sort(m), js, side="left") - js - 1
bons = js[Sg % 2 == 0]
viol = []
for a, b in zip(bons, bons[1:]):
    z = sum(cont.get(int(j), 0) for j in range(a, b))
    if z != b - a:
        viol.append({"g_inicio": int(a), "comprimento": int(b - a), "zeros": z})
grupos = []
for v in viol:
    if grupos and grupos[-1][-1]["g_inicio"] + grupos[-1][-1]["comprimento"] == v["g_inicio"]:
        grupos[-1].append(v)
    else:
        grupos.append([v])
iM, im = int(np.argmax(S_dep)), int(np.argmin(S_dep - 1))
maximo = max(dist)
out = {"zeros": len(idx), "intervalos_de_gram": m1 - m0,
       "zeros_por_intervalo": {str(k): v for k, v in sorted(dist.items())},
       "pontos_de_gram_ruins_%": round(100 * (1 - len(bons) / (m1 - m0 + 1)), 2),
       "excecoes_de_Rosser": len(grupos), "blocos_fora_de_Rosser": len(viol), "excecoes": grupos[:50],
       "S_max": float(S_dep[iM]), "S_max_logo_depois_do_zero": int(idx[iM]), "S_max_altura": rows[iM][1],
       "S_min": float(S_dep[im] - 1), "S_min_logo_antes_do_zero": int(idx[im]), "S_min_altura": rows[im][1],
       "desvio_padrao_S": float(np.std(S_dep - 0.5)),
       "intervalos_com_mais_zeros": [{"g": j, "zeros": [int(k) for k in idx[m == j]],
                                      "alturas": [rows[i][1] for i in np.nonzero(m == j)[0]]}
                                     for j, c in cont.items() if c == maximo and maximo >= 4]}
(SAI / "gram.json").write_text(json.dumps(out, ensure_ascii=False, indent=1) + "\n")
print(json.dumps({k: v for k, v in out.items() if k != "excecoes"}, ensure_ascii=False, indent=1))
