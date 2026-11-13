"""Pontes no eixo Riemann: confere numericamente o que ClayRiemannProof/EixoRiemann/Pontes.lean prova.

Uso: python3 test_pontes.py [pasta com zeta_dp.py]
"""
import cmath
import itertools
import random
import sys

sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else '.')
from zeta_dp import zeta, Z  # noqa: E402

falhas = []


def confere(nome, ok, detalhe=''):
    print(('ok    ' if ok else 'FALHA ') + nome + ('  ' + detalhe if detalhe else ''))
    if not ok:
        falhas.append(nome)


def refina(g):
    for _ in range(8):
        h = 1e-6
        g -= Z(g) / ((Z(g + h) - Z(g - h)) / (2 * h))
    return g


G0 = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062, 37.586178, 40.918719, 43.327073, 48.005151, 49.773832]
G = [refina(g) for g in G0]
TRIV = [-2.0, -4.0, -6.0, -8.0, -10.0]
TOL = 1e-9


def segura(z1, z2):
    return abs(zeta(z1)) < TOL and abs(zeta(z2)) < TOL


# 1. todas as pontes entre zeros conhecidos seguram: n(n-1) com delta != 0
for nome, nt in (('5 triviais + 5 na reta (ate 32,93)', 5), ('5 triviais + 10 na reta (ate 49,77)', 10)):
    zs = TRIV + [0.5 + 1j * g for g in G[:nt]]
    pontes = [(a, b) for a, b in itertools.permutations(zs, 2)]
    confere(f'pontes com delta != 0 entre {nome}: todas seguram', all(segura(a, b) for a, b in pontes),
            f'{len(pontes)} pontes')

# 2. com t arredondado em 2 casas a ponte nao segura: delta tem que ser o exato
d_exato = G[1] - G[0]
confere('delta exato rho1 -> rho2 = 6,887314...i; com 0,5 + 21,02i arredondado nao e zero',
        abs(zeta(0.5 + 21.02j)) > 1e-3, f'delta = {d_exato:.9f}i, |zeta(0,5+21,02i)| = {abs(zeta(0.5 + 21.02j)):.4f}')

# 3. a ponte so tem duas pontas: e -> c respeita o produto de Idem so para c = 0, 1
rng = random.Random(7)


def idem_mul(x, y):
    return (x[0] * y[0], x[0] * y[1] + x[1] * y[0] + x[1] * y[1])


def avalia(c, x):
    return x[0] + c * x[1]


def rc():
    return complex(rng.uniform(-2, 2), rng.uniform(-2, 2))


res = {}
for c in (0, 1, 0.25, 0.5, 0.75):
    erro = 0.0
    for _ in range(500):
        x, y = (rc(), rc()), (rc(), rc())
        erro = max(erro, abs(avalia(c, idem_mul(x, y)) - avalia(c, x) * avalia(c, y)))
    res[c] = erro
confere('e -> c e homomorfismo so em c = 0 e c = 1 (e = 0,25 / 0,5 / 0,75 nao sao pontos de Idem)',
        res[0] < 1e-12 and res[1] < 1e-12 and min(res[0.25], res[0.5], res[0.75]) > 0.1,
        ', '.join(f'c={c}: {e:.1e}' for c, e in res.items()))

# 4. quarteto como operador: Klein permuta as coordenadas de Q
def esp(s): return s.conjugate()
def ten(s): return 1 - s
def tor(s): return 1 - s.conjugate()


def Q(s):
    return (zeta(s), zeta(ten(s)), zeta(esp(s)), zeta(tor(s)))


ok = True
for s in (0.6 + 14.13j, 0.3 + 25j, 0.8 + 40.5j, 0.45 + 7j):
    q = Q(s)
    for op, perm in ((esp, (2, 3, 0, 1)), (ten, (1, 0, 3, 2)), (tor, (3, 2, 1, 0))):
        q2 = Q(op(s))
        ok &= all(abs(q2[k] - q[perm[k]]) < 1e-9 for k in range(4))
confere('Q(espelho s), Q(tensao s), Q(torcao s) = permutacoes de Q(s)', ok)

# 5. ponte horizontal: delta = 1 - 2 Re(rho), so existe se houver zero fora; nos pontos testados nao segura
for s in (0.6 + 1j * G[0], 0.7 + 1j * G[1], 0.4 + 1j * G[0]):
    d = 1 - 2 * s.real
    a, b = zeta(s), zeta(s + d)
    confere(f'ponte horizontal {s.real:.1f}+{s.imag:.2f}i -> {(s + d).real:.1f}+{s.imag:.2f}i (delta = {d:+.1f}) nao segura',
            abs(a) > 0.05 and abs(b) > 0.05, f'|zeta| = {abs(a):.5f}, {abs(b):.5f}')

# 6. F = |zeta(s)|^2 + |zeta(1-s)|^2 fora da reta: o infimo e 0, nao 0,000126
vals = []
for eps in (1e-2, 1e-3, 1e-4, 1e-5):
    s = 0.5 - eps + 1j * G[0]
    vals.append(abs(zeta(s)) ** 2 + abs(zeta(1 - s)) ** 2)
confere('F(0,5 - eps + i g1) -> 0 como eps^2: nao ha minimo positivo fora da reta',
        all(vals[k + 1] < vals[k] / 50 for k in range(3)) and vals[-1] < 1e-9,
        ', '.join(f'{v:.2e}' for v in vals))

# 7. iteracao 4 -> 16 -> 256 -> 65536 -> 4294967296: |Z0|^(2^k), tuplas dos mesmos 4 zeros
seq = [4 ** (2 ** k) for k in range(5)]
confere('|Z0|^(2^k) = 4, 16, 256, 65 536, 4 294 967 296; passa de 7 milhoes so em k = 4',
        seq == [4, 16, 256, 65536, 4294967296] and seq[3] < 7_000_000 < seq[4])

print()
print(f'{len(falhas)} falha(s)')
sys.exit(1 if falhas else 0)
