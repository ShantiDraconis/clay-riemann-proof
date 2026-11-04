"""Princípio do argumento adaptativo: quantos zeros com 0,505 < Re s < 3, em faixas de altura 2.

    python3 argumento.py NOME > argumento_NOME.json      (NOME = dh ou epstein)

Conta, para Davenport–Heilbronn (até Im 170) e Epstein m² + 5n² (até Im 100), os zeros à direita da reta em cada
retângulo [0,505; 3] × [y; y + 2], pela variação do argumento de f no bordo (subdivisão adaptativa até cada passo
de argumento ficar abaixo de 0,3 rad). Pela simetria s ↦ 1 − s̄, cada zero contado é metade de um par fora da reta.
Zeros com 0,5 < Re s ≤ 0,505 escapam desta conta; a contagem na reta (S_reta, padrao_fora.py) os pegaria.
Numérico (mpmath, 15 dígitos), sem certificação.
"""
import json
import math
import sys

sys.path.insert(0, "/home/claude/ext/mpmath")
from mpmath import mp, mpc, dirichlet, zeta, sqrt

mp.dps = 15
NOME = sys.argv[1]
kap = (sqrt(10 - 2 * sqrt(5)) - 2) / (sqrt(5) - 1)
CHI5, CHI5B = [0, 1, 1j, -1j, -1], [0, 1, -1j, 1j, -1]
CHI_4, LEG5 = [0, 1, 0, -1], [0, 1, -1, -1, 1]
CHI_20 = [CHI_4[n % 4] * LEG5[n % 5] for n in range(20)]
if NOME == "dh":
    f = lambda s: (1 - 1j * kap) / 2 * dirichlet(s, CHI5) + (1 + 1j * kap) / 2 * dirichlet(s, CHI5B)
    TOPO = 170
else:
    f = lambda s: zeta(s) * dirichlet(s, CHI_20) + dirichlet(s, CHI_4) * dirichlet(s, LEG5)
    TOPO = 100
X0, X1 = 0.505, 3.0


def dang(a, b):
    r = complex(b) / complex(a)
    return math.atan2(r.imag, r.real)


def seg(p, q, fp, fq, prof=0):
    d = dang(fp, fq)
    if abs(d) < 0.3 or prof > 22:
        return d, prof > 22
    m = (p + q) / 2
    fm = f(m)
    d1, e1 = seg(p, m, fp, fm, prof + 1)
    d2, e2 = seg(m, q, fm, fq, prof + 1)
    return d1 + d2, e1 or e2


def faixa(y):
    y1 = min(y + 2, TOPO)
    cant = [mpc(X0, y), mpc(X1, y), mpc(X1, y1), mpc(X0, y1)]
    tot, ruim = 0.0, False
    for a, b in zip(cant, cant[1:] + cant[:1]):
        k = max(4, int(abs(complex(b - a)) / 0.1))
        pts = [a + (b - a) * j / k for j in range(k + 1)]
        vals = [f(p) for p in pts]
        for p, q, fp, fq in zip(pts, pts[1:], vals, vals[1:]):
            d, e = seg(p, q, fp, fq)
            tot += d
            ruim = ruim or e
    c = tot / (2 * math.pi)
    return {"Im_de": y, "Im_ate": y1, "zeros": round(c), "desvio": abs(c - round(c)), "suspeito": ruim}


res = []
y = 1.0
while y < TOPO - 1e-9:
    r = faixa(y)
    res.append(r)
    print(r, file=sys.stderr, flush=True)
    y += 2
print(json.dumps({"funcao": NOME, "Re": [X0, X1], "faixas": res, "total": sum(r["zeros"] for r in res),
                  "desvio_max": max(r["desvio"] for r in res)}, ensure_ascii=False))
