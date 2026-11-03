"""Todas as lombadas de Z entre zeros consecutivos de uma lista certificada (estimativa por Riemann–Siegel).

    python3 lombadas.py SAIDA.json LISTA.csv.gz

Para cada par de zeros consecutivos γ_k < γ_{k+1}: Z, Z', Z'' no ponto médio numa só passada da soma de
Riemann–Siegel (Z = 2Σ n^{−½} cos φ_n + R, Z' = −2Σ n^{−½} k_n sen φ_n, Z'' = −2Σ n^{−½} k_n² cos φ_n, com
φ_n = θ(t) − t log n e k_n = θ'(t) − log n), um passo de Newton para o extremo t* = m − Z'/Z'' e a altura
Z* = Z − Z'²/(2Z''). O sinal de Z* alterna de uma lombada para a outra. Fora do kernel; ponto flutuante.
"""
import gzip
import json
import math
import sys
import time
from decimal import Decimal, getcontext

import numpy as np

getcontext().prec = 60
SAI, LISTA = sys.argv[1], sys.argv[2]
PI = Decimal("3.14159265358979323846264338327950288419716939937510582097494459230781640628620899")
DOISPI = 2 * PI


def theta(t):
    return (t / 2) * (t / (2 * PI)).ln() - t / 2 - PI / 8 + 1 / (48 * t) + Decimal(7) / (5760 * t ** 3)


idx, gam = [], []
for ln in gzip.open(LISTA, "rt"):
    if ln[0].isdigit():
        a = ln.strip().split(",")
        idx.append(int(a[0]))
        gam.append(Decimal(a[1]))
n = len(gam)
T0 = int(gam[0])
NMAX = int(math.sqrt(float(gam[-1]) / (2 * math.pi))) + 2
crivo = np.ones(NMAX + 1, dtype=bool)
crivo[:2] = False
for q in range(2, int(NMAX ** 0.5) + 1):
    if crivo[q]:
        crivo[q * q::q] = False
primos = np.nonzero(crivo)[0]
logp = {int(q): Decimal(int(q)).ln() for q in primos}
menor = np.zeros(NMAX + 1, dtype=np.int64)
for q in primos[::-1]:
    menor[q::q] = q
logD = [Decimal(0)] * (NMAX + 1)
for m in range(2, NMAX + 1):
    q = int(menor[m])
    logD[m] = logD[m // q] + logp[q]
fase0 = np.array([float((T0 * logD[m]) % DOISPI) for m in range(1, NMAX + 1)])
logf = np.array([float(logD[m]) for m in range(1, NMAX + 1)])
amp = 1 / np.sqrt(np.arange(1, NMAX + 1, dtype=np.float64))
print(f"{n} zeros; fases prontas", flush=True)


def jato(t):
    """Z, Z', Z'' em t (Decimal)."""
    tf = float(t)
    a = math.sqrt(tf / (2 * math.pi))
    N = int(a)
    p = a - N
    fase = float(theta(t) % DOISPI) - fase0[:N] - float(t - T0) * logf[:N]
    k = 0.5 * math.log(tf / (2 * math.pi)) - logf[:N]
    c, s = np.cos(fase), np.sin(fase)
    w = amp[:N]
    z = 2 * float(np.dot(w, c)) + (-1) ** (N - 1) * (tf / (2 * math.pi)) ** -0.25 * \
        math.cos(2 * math.pi * (p * p - p - 1 / 16)) / math.cos(2 * math.pi * p)
    z1 = -2 * float(np.dot(w * k, s))
    z2 = -2 * float(np.dot(w * k * k, c))
    return z, z1, z2


lomb = []
t0 = time.time()
for i in range(n - 1):
    m = (gam[i] + gam[i + 1]) / 2
    D = float(gam[i + 1] - gam[i])
    z, z1, z2 = jato(m)
    d = -z1 / z2 if z2 else 0.0
    if abs(d) < D / 2:
        ze, zpp, ts = z - z1 * z1 / (2 * z2), z2, m + Decimal(d)
    else:  # extremo longe do meio (lombada torta): fica com o meio
        ze, zpp, ts = z, z2, m
    lomb.append([idx[i], D, ze, zpp, str(ts)])
    if i % 2000 == 0:
        print(i, round(time.time() - t0, 1), flush=True)
json.dump({"lista": LISTA, "zeros": n, "colunas": ["indice", "intervalo", "Z_estrela", "Zpp", "t_estrela"],
           "lombadas": lomb}, open(SAI, "w"))
print("fim", round(time.time() - t0, 1))
