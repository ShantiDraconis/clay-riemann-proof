"""No-go do Gram de primos: homogeneidade, média em t e frequências.

Uso: python3 test_gram_no_go.py
"""
import math
import sys

import numpy as np

falhas = []


def confere(nome, ok, detalhe=''):
    print(('ok    ' if ok else 'FALHA ') + nome + ('  ' + detalhe if detalhe else ''))
    if not ok:
        falhas.append(nome)


def primos(n):
    crivo = np.ones(n + 1, bool)
    crivo[:2] = False
    for k in range(2, int(n ** 0.5) + 1):
        if crivo[k]:
            crivo[k * k::k] = False
    return np.nonzero(crivo)[0]


P = primos(100)
rng = np.random.default_rng(1)
a = rng.normal(size=len(P)) + 1j * rng.normal(size=len(P))
logp = np.log(P.astype(float))


def soma(a, t):
    return (a[None, :] * np.exp(-1j * np.outer(t, logp))).sum(axis=1)


# 1. homogeneidade: dobrar os coeficientes multiplica por 4 (W linear multiplicaria por 2)
t = np.linspace(-50, 50, 2001)
r = np.abs(soma(2 * a, t)) ** 2 / np.abs(soma(a, t)) ** 2
confere('S_T(2 phi) = 4 S_T(phi) em todo t (forma linear teria fator 2)', np.allclose(r, 4), f'razao = {r.mean():.6f}')

# 2. media em t: os termos cruzados somem, sobra a diagonal sum |a_p|^2
diag = np.sum(np.abs(a) ** 2)
res = []
for T in (10, 100, 1000, 10000):
    tt = np.linspace(-T, T, 200 * T + 1)
    media = np.trapezoid(np.abs(soma(a, tt)) ** 2, tt) / (2 * T)
    res.append(abs(media - diag) / diag)
confere('media de |sum a_p p^(-it)|^2 em [-T, T] -> sum |a_p|^2 (cruzados ~ 1/T)',
        res[-1] < 2e-3 and res[-1] < res[0], ', '.join(f'T={T}: {e:.1e}' for T, e in zip((10, 100, 1000, 10000), res)))

# 3. frequencias: q/p nunca e inteiro para primos distintos (ate 10 000)
Pg = primos(10_000)
achou = 0
for i, p in enumerate(Pg):
    for q in Pg[i + 1:]:
        if q % p == 0:
            achou += 1
confere('q/p nunca e inteiro para primos p < q ate 10 000: log(q/p) nunca e log n', achou == 0,
        f'{len(Pg) * (len(Pg) - 1) // 2} pares')
pot = np.array([n for n in range(2, 2000) if len({int(p) for p in primos(n) if n % p == 0}) == 1], float)
freq_gram = np.abs(np.subtract.outer(logp, logp)).ravel()  # 0 (diagonal) e |log(q/p)|
dist = np.min(np.abs(np.subtract.outer(freq_gram, np.log(pot))))
confere('nenhuma frequencia do Gram (0 ou log(q/p), p, q < 100) e log de potencia de primo ate 2000',
        dist > 1e-6, f'{len(pot)} potencias, distancia minima = {dist:.2e}')

print()
print(f'{len(falhas)} falha(s)')
sys.exit(1 if falhas else 0)
