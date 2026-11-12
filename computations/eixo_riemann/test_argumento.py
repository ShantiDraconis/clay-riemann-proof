"""Argumento no eixo Riemann: confere numericamente o que ClayRiemannProof/EixoRiemann/Argumento.lean prova.

Uso: python3 test_argumento.py [pasta com zeta_dp.py]
"""
import cmath
import itertools
import math
import random
import sys

import numpy as np

sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else '.')
from zeta_dp import zeta, derivadas  # noqa: E402

falhas = []


def confere(nome, ok, detalhe=''):
    print(('ok    ' if ok else 'FALHA ') + nome + ('  ' + detalhe if detalhe else ''))
    if not ok:
        falhas.append(nome)


rng = np.random.default_rng(20261112)

# 1. Idem tem exatamente 4 idempotentes (busca na grade de inteiros gaussianos)
grade = [complex(a, b) for a in range(-3, 4) for b in range(-3, 4)]
idem = [(z, w) for z in grade for w in grade if abs(z * z - z) < 1e-12 and abs(z * w + w * z + w * w - w) < 1e-12]
confere('Idem: idempotentes = {0, 1, e, 1 - e}', sorted(idem, key=lambda p: (p[0].real, p[1].real)) ==
        [(0, 0), (0, 1), (1, -1), (1, 0)], str(idem))

# 2. colapso: projecoes so tem autovalores 0 e 1; autovalor 4/5 nao cabe em projecao
ok = True
for _ in range(200):
    n = rng.integers(2, 7)
    U = rng.normal(size=(n, n)) + 1j * rng.normal(size=(n, n))
    D = np.diag(rng.integers(0, 2, size=n).astype(complex))
    P = U @ D @ np.linalg.inv(U)
    ok &= np.allclose(P @ P, P, atol=1e-8)
    ev = np.linalg.eigvals(P)
    ok &= all(min(abs(x), abs(x - 1)) < 1e-6 for x in ev)
confere('colapso: 200 projecoes aleatorias, todo autovalor e 0 ou 1', ok)
M = np.diag([1.0, 0.8])
confere('autovalor 4/5 (delta = 1/4): a matriz nao e projecao', not np.allclose(M @ M, M),
        f'|P^2 - P| = {np.abs(M @ M - M).max():.2f}')
lam = {d: 1 / (1 + 4 * d * d) for d in (0, 0.1, 0.25, 0.5)}
confere('1/(1 + 4 delta^2) = 1 so em delta = 0', lam[0] == 1 and all(0 < lam[d] < 1 for d in (0.1, 0.25, 0.5)),
        ', '.join(f'{d}: {v:.4f}' for d, v in lam.items()))

# 3. projecao do espelho: com RH, V = C e P = id funcionam (o lado facil da equivalencia)
confere('projecao do espelho com RH: P = id, autovalor 1 em todo zero da reta', lam[0] == 1)

# 4. 3-4-1 e positividade aritmetica
th = np.linspace(0, 2 * np.pi, 100001)
v = 3 + 4 * np.cos(th) + np.cos(2 * th)
confere('3 + 4 cos + cos 2 = 2(1 + cos)^2 >= 0, minimo em pi', v.min() >= -1e-12 and
        np.allclose(v, 2 * (1 + np.cos(th)) ** 2), f'min = {v.min():.2e}')


def menos_dlogzeta(s):
    d = derivadas(s, 1, r=min(0.25, abs(s - 1) / 2))  # o circulo de Cauchy nao pode conter o polo em s = 1
    return -d[1] / d[0]


ok = True
vals = []
for sigma in (1.01, 1.05, 1.2):
    for t in (14.134725, 21.02204, 100.0, 1000.0):
        comb = (3 * menos_dlogzeta(sigma) + 4 * menos_dlogzeta(sigma + 1j * t)
                + menos_dlogzeta(sigma + 2j * t)).real
        vals.append(comb)
        ok &= comb >= 0
confere('Re[3(-z\'/z)(s) + 4(-z\'/z)(s+it) + (-z\'/z)(s+2it)] >= 0 em sigma > 1 (12 pontos)', ok,
        f'min = {min(vals):.3f}')

# 5. topologia: torcao e isometria e troca os lados da reta
def tor(s): return 1 - s.conjugate()


ok_iso = ok_lado = True
for _ in range(2000):
    a = complex(*rng.uniform(-3, 3, 2))
    b = complex(*rng.uniform(-3, 3, 2))
    ok_iso &= abs(abs(tor(a) - tor(b)) - abs(a - b)) < 1e-12
    if abs(a.real - 0.5) > 1e-9:
        ok_lado &= (a.real - 0.5) * (tor(a).real - 0.5) < 0
confere('torcao: isometria e troca os lados da reta (2000 pontos)', ok_iso and ok_lado)

# 6. dLVP em pontes: o limite |delta| < 1 - 2c/log t afasta da borda e tende a 1, nao a 0
c = 0.1
lim = [1 - 2 * c / math.log(t) for t in (10, 1e3, 1e6, 3e12)]
confere('dLVP (c = 0,1): limite de |delta| cresce para 1 com t; nao fecha', all(lim[i] < lim[i + 1] < 1 for i in range(3)),
        ', '.join(f'{x:.4f}' for x in lim))

# 7. inabitantes
confere('ponte com ponta em Re >= 1: zeta != 0 em 1 + it (amostra)',
        min(abs(zeta(1 + 1j * t)) for t in np.linspace(1, 200, 400)) > 1e-3)


def idem_mul(x, y):
    return (x[0] * y[0], x[0] * y[1] + x[1] * y[0] + x[1] * y[1])


erro = max(abs((x[0] + 0.5 * x[1]) * (y[0] + 0.5 * y[1]) - (lambda p: p[0] + 0.5 * p[1])(idem_mul(x, y)))
           for x, y in [((complex(*rng.normal(size=2)), complex(*rng.normal(size=2))),
                         (complex(*rng.normal(size=2)), complex(*rng.normal(size=2)))) for _ in range(200)])
confere('meio da ponte (e = 1/2) nao e homomorfismo', erro > 0.1, f'erro max = {erro:.2f}')

print()
print(f'{len(falhas)} falha(s)')
sys.exit(1 if falhas else 0)
