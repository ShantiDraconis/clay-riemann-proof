"""Onde os zeros de ζ chegam mais perto um do outro (e da colisão que os tiraria da reta), na lista contígua completa.

    python3 aproximacoes.py pasta_c1 pasta_c2 > aproximacoes.json

Entrada: os zeros certificados (Arb, bolas ≤ 5,01·10⁻¹⁸, déficit 0) das duas continuações contíguas:
c1 = 4 faixas de 3 000 175 342 471,5 a …822 471,5 (2 054 383 zeros); c2 = 24 faixas de …822 471,5 a
3 000 178 702 471,5 (12 326 300 zeros). Só análises completas: nada aqui usa faixas ainda em execução.

Saídas (todas fora do kernel):
1. cauda dos espaçamentos pequenos: F(x) = fração de espaçamentos normalizados s < x, com o expoente ajustado em
   0,01 ≤ x ≤ 0,1, contra GUE (Wigner: erf(2x/√π) − (4x/π)e^{−4x²/π} ≈ 1,08 x³), GOE (≈ (π²/12) x²) e Poisson (≈ x);
2. o menor espaçamento em blocos de n zeros (mediana sobre os blocos) contra a previsão (ln 2 · 9/(π² n))^{1/3};
3. os 30 pares mais próximos: altura, Δγ, s, λ ≈ −Δγ²/2 (tempo de colisão no fluxo de de Bruijn, x = 2γ),
   espaçamentos vizinhos e S(t) logo depois do par;
4. o que acontece em volta de um quase-encontro: média dos espaçamentos vizinhos condicionada a s pequeno.
"""
import gzip
import json
import math
import sys
from decimal import Decimal
from pathlib import Path

import numpy as np

sys.path.insert(0, "/home/claude/ext/mpmath")
from mpmath import mp, mpf, siegeltheta, pi as mpi, log as mlog, floor as mfloor, erf as merf, exp as mexp

C0 = Decimal("3000175342471.5")
N0 = 12363153478531
idx_l, h_l, t_txt = [], [], []
for pasta, faixas in ((sys.argv[1], range(4)), (sys.argv[2], range(24))):
    for I in faixas:
        for linha in gzip.open(Path(pasta) / f"zeros{I}.csv.gz", "rt"):
            if linha.startswith("indice"):
                continue
            i, m, _ = linha.strip().split(",")
            idx_l.append(int(i))
            h_l.append(float(Decimal(m) - C0))
            t_txt.append(m)
idx = np.array(idx_l, dtype=np.int64)
h = np.array(h_l)
assert idx[0] == N0 + 1 and np.all(np.diff(idx) == 1) and np.all(np.diff(h) > 0)
n = len(h)
T = 3.0001770e12
dens = math.log(T / (2 * math.pi)) / (2 * math.pi)           # zeros por unidade de altura
# densidade local (varia 1,6·10⁻⁸ relativo na faixa: desprezível, mas usada assim mesmo)
dloc = np.log((3000175342471.5 + h[:-1]) / (2 * math.pi)) / (2 * math.pi)
gaps = np.diff(h)
s = gaps * dloc

# 1. cauda
xs = np.logspace(-3, 0, 31)
ss = np.sort(s)
F = np.searchsorted(ss, xs) / len(ss)


def gue(x):
    x = mpf(x)
    return float(merf(2 * x / mp.sqrt(mpi)) - (4 * x / mpi) * mexp(-4 * x * x / mpi))


cauda = [{"x": float(x), "F": float(f), "contagem": int(round(f * len(ss))), "GUE": gue(x),
          "GOE_pequeno": math.pi ** 2 / 12 * x ** 2, "Poisson": 1 - math.exp(-x)} for x, f in zip(xs, F)]
sel = (xs >= 0.01) & (xs <= 0.1) & (F > 0)
expo, c = np.polyfit(np.log(xs[sel]), np.log(F[sel]), 1)

# 2. menor espaçamento por bloco
blocos = []
for m in [10 ** 3, 3 * 10 ** 3, 10 ** 4, 3 * 10 ** 4, 10 ** 5, 3 * 10 ** 5, 10 ** 6, 3 * 10 ** 6, 10 ** 7]:
    k = len(s) // m
    if k < 1:
        continue
    mins = s[:k * m].reshape(k, m).min(axis=1)
    blocos.append({"n": m, "blocos": k, "mediana_do_minimo": float(np.median(mins)),
                   "previsto_GUE": (math.log(2) * 9 / (math.pi ** 2 * m)) ** (1 / 3)})

# S(t) logo depois de cada zero (θ/π por Taylor em C0; termo cúbico < 10⁻⁶)
mp.dps = 50
t0 = mpf(str(C0))
th0 = siegeltheta(t0) / mpi
A = int(mfloor(th0))
B, Cc = float(mlog(t0 / (2 * mpi)) / 2 / mpi), float(1 / (4 * mpi * t0))
for k in (0, n // 2, n - 1):
    assert abs(float(siegeltheta(mpf(t_txt[k])) / mpi - A) - (float(th0 - A) + B * h[k] + Cc * h[k] ** 2)) < 1e-6
S_dep = (idx - A) - (float(th0 - A) + B * h + Cc * h * h) - 1

# 3. os pares mais próximos
ordem = np.argsort(gaps)
pares = []
for k in ordem[:30]:
    k = int(k)
    pares.append({
        "zeros": [int(idx[k]), int(idx[k + 1])], "t": t_txt[k], "Delta_gamma": float(gaps[k]), "s": float(s[k]),
        "lambda_colisao": -float(gaps[k]) ** 2 / 2,
        "s_vizinho_antes": float(s[k - 1]) if k > 0 else None,
        "s_vizinho_depois": float(s[k + 1]) if k + 1 < len(s) else None,
        "S_depois_do_par": float(S_dep[k + 1]),
    })

# 4. vizinhos de um quase-encontro
viz = []
for lo, hi in [(0, 0.02), (0.02, 0.05), (0.05, 0.1), (0.1, 0.3), (0.3, 0.7), (0.7, 1.3), (1.3, 2.0), (2.0, 4.0)]:
    msk = (s[1:-1] >= lo) & (s[1:-1] < hi)
    if msk.sum() == 0:
        continue
    vv = np.concatenate([s[:-2][msk], s[2:][msk]])
    viz.append({"s_do_par": [lo, hi], "pares": int(msk.sum()), "media_dos_vizinhos": float(vv.mean()),
                "soma_vizinho_par_vizinho": float((s[:-2][msk] + s[1:-1][msk] + s[2:][msk]).mean())})

print(json.dumps({
    "zeros": n, "de": str(C0), "ate": "3000178702471.5", "espacamentos": len(s),
    "variancia_s": float(s.var()), "variancia_GUE": 3 * math.pi / 8 - 1,
    "cauda": cauda, "expoente_cauda_0.01_0.1": float(expo), "constante_cauda": float(math.exp(c)),
    "expoente_GUE": 3, "constante_GUE_pequeno": math.pi ** 2 / 9,
    "minimo_por_bloco": blocos, "pares_mais_proximos": pares, "vizinhos": viz,
    "S_max": float(S_dep.max()), "S_min": float((S_dep - 1).min()),
}, ensure_ascii=False, indent=1))
