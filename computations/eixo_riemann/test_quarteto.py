"""Quartetos, Idem e C^4: confere numericamente o que ClayRiemannProof/EixoRiemann/Quarteto.lean prova.

Uso: python3 test_quarteto.py [pasta com zeta_dp.py]
"""
import cmath
import itertools
import math
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else '.')
from zeta_dp import zeta, derivadas, Z  # noqa: E402

falhas = []


def confere(nome, ok, detalhe=''):
    print(('ok    ' if ok else 'FALHA ') + nome + ('  ' + detalhe if detalhe else ''))
    if not ok:
        falhas.append(nome)


# ---------- 1. Grupo de Klein, em racionais exatos (s = (re, im)) ----------
def esp(s): return (s[0], -s[1])
def ten(s): return (1 - s[0], -s[1])
def tor(s): return (1 - s[0], s[1])
def orb(s): return frozenset({s, esp(s), ten(s), tor(s)})


rng = random.Random(20261112)
pts = [(F(rng.randint(-40, 40), 20), F(rng.randint(-40, 40), 7)) for _ in range(500)]
confere('Klein: espelho e tensao sao involucoes, espelho*tensao = torcao',
        all(esp(esp(s)) == s and ten(ten(s)) == s and ten(esp(s)) == tor(s) and esp(ten(s)) == tor(s)
            for s in pts))

meio = F(1, 2)
tam = {}
for s in pts:
    chave = (s[0] != meio, s[1] != 0)
    tam.setdefault(chave, set()).add(len(orb(s)))
confere('quarteto: 4 pontos fora da reta e fora do eixo real', tam.get((True, True)) == {4}, str(tam))
confere('quarteto: 2 pontos na reta (t != 0)', tam.get((False, True), {2}) == {2})
confere('quarteto: s = 1/2 fica sozinho', len(orb((meio, F(0)))) == 1)

# ---------- 2. Nao existem quartetos conectados (busca exaustiva numa grade) ----------
grade = [(F(a, 10), F(b, 3)) for a in range(-5, 16) for b in range(-6, 7)]
parciais = 0
pares = 0
for s, t in itertools.combinations(grade, 2):
    pares += 1
    A, B = orb(s), orb(t)
    inter = A & B
    if inter and A != B:
        parciais += 1
confere(f'quartetos iguais ou disjuntos: {pares} pares da grade, interseccao parcial', parciais == 0,
        f'parciais = {parciais}')

# ---------- 3. Contagem: 4k fora da reta, 2k na metade de cima; reta soma 1 por zero em t > 0 ----------
ok_cont = True
for _ in range(300):
    k = rng.randint(0, 6)
    m = rng.randint(0, 4)
    reps = set()
    while len(reps) < k:
        reps.add((F(rng.randint(11, 19), 20), F(rng.randint(1, 60), 4)))  # 1/2 < re < 1, im > 0
    S = set()
    for r in reps:
        S |= orb(r)
    reta = set()
    while len(reta) < m:
        reta.add((meio, F(rng.randint(1, 60), 4)))
    for r in reta:
        S |= orb(r)
    fora = {s for s in S if s[0] != meio}
    cima = {s for s in S if s[1] > 0}
    cima_fora = {s for s in fora if s[1] > 0}
    if not (len(fora) == 4 * k and len(cima_fora) == 2 * k and len(cima) == 2 * k + m):
        ok_cont = False
confere('contagem: #fora = 4k, #fora com Im>0 = 2k, N(T) = 2k + (zeros na reta)', ok_cont)
confere('1 quarteto + 1 zero na reta no mesmo t: 6 pontos, 3 com Im > 0',
        (lambda S: (len(S), len({s for s in S if s[1] > 0})))(orb((F(3, 5), F(1413, 100))) | orb((meio, F(1413, 100))))
        == (6, 3))

# ---------- 4. Idem = C x C ----------
def idem_mul(x, y):
    return (x[0] * y[0], x[0] * y[1] + x[1] * y[0] + x[1] * y[1])


def par(x):
    return (x[0], x[0] + x[1])


def rc():
    return complex(rng.uniform(-3, 3), rng.uniform(-3, 3))


ok_iso = ok_ass = True
for _ in range(2000):
    x, y, w = (rc(), rc()), (rc(), rc()), (rc(), rc())
    p = par(idem_mul(x, y))
    q = (par(x)[0] * par(y)[0], par(x)[1] * par(y)[1])
    ok_iso &= abs(p[0] - q[0]) + abs(p[1] - q[1]) < 1e-9
    a = idem_mul(idem_mul(x, y), w)
    b = idem_mul(x, idem_mul(y, w))
    ok_ass &= abs(a[0] - b[0]) + abs(a[1] - b[1]) < 1e-9
confere('Idem: (z, w) -> (z, z + w) preserva o produto (2000 pares)', ok_iso)
confere('Idem: associativa (2000 trios)', ok_ass)


# ---------- 5. zeta no eixo: zeros com delta != 0 ----------
def refina(g):
    for _ in range(8):
        h = 1e-6
        g -= Z(g) / ((Z(g + h) - Z(g - h)) / (2 * h))
    return g


g1, g2 = refina(14.134725141734693), refina(21.022039638771555)
rho1, rho2 = 0.5 + 1j * g1, 0.5 + 1j * g2


def zeta_idem(z, w):
    return (zeta(z), zeta(z + w))


TOL = 1e-9
casos = [
    ('-2 carrega -4: N = -2 + (-2)e', -2, -2),
    ('-2 carrega 0,5+14,13i: N = -2 + (2,5 + i g1)e', -2, 2.5 + 1j * g1),
    ('rho1 carrega 1 - rho1: N = rho1 + (1 - 2 rho1)e, delta = -2i g1', rho1, 1 - 2 * rho1),
    ('rho1 carrega rho2: N = rho1 + (rho2 - rho1)e, delta = i(g2 - g1)', rho1, rho2 - rho1),
]
for nome, z, w in casos:
    a, b = zeta_idem(z, w)
    confere('zero em Idem com delta != 0: ' + nome, abs(a) < TOL and abs(b) < TOL and abs(w) > 1,
            f'|zeta(z)| = {abs(a):.1e}, |zeta(z+delta)| = {abs(b):.1e}, |delta| = {abs(w):.3f}')

# eixo puro: coeficiente exato zeta(c) - zeta(0)
c2 = zeta(2) - zeta(0)
confere('eixo puro, c = 2: coeficiente = pi^2/6 + 1/2 (proposto: -5,85059)',
        abs(c2 - (math.pi ** 2 / 6 + 0.5)) < 1e-12, f'{c2.real:.6f}')
confere('eixo puro: primeiro componente zeta(0) = -1/2 != 0', abs(zeta(0) + 0.5) < 1e-12)


# ---------- 6. C^4 ----------
def c4_mul(x, y):
    return tuple(a * b for a, b in zip(x, y))


e = [tuple(1 if i == j else 0 for j in range(4)) for i in range(4)]
confere('C^4: e_i^2 = e_i, e_i e_j = 0 (i != j), soma = 1',
        all(c4_mul(e[i], e[i]) == e[i] for i in range(4))
        and all(c4_mul(e[i], e[j]) == (0, 0, 0, 0) for i in range(4) for j in range(4) if i != j)
        and tuple(map(sum, zip(*e))) == (1, 1, 1, 1))


def Q(s):
    return (zeta(s), zeta(1 - s), zeta(s.conjugate()), zeta(1 - s.conjugate()))


q1 = Q(rho1)
confere('Q(rho1) = 0 nas 4 coordenadas (rho1 na reta: so 2 pontos distintos)', max(map(abs, q1)) < TOL,
        f'max = {max(map(abs, q1)):.1e}')
q6 = Q(0.6 + 1j * g1)
confere('Q(0,6 + i g1): nenhuma coordenada zero', min(map(abs, q6)) > 0.07,
        ', '.join(f'{abs(v):.6f}' for v in q6))
# Q(s) = 0 <=> zeta(s) = 0: |zeta(1-s)| / |zeta(s)| e o fator da equacao funcional, finito e nao nulo
razoes = [abs(zeta(1 - s)) / abs(zeta(s)) for s in (0.6 + 14j, 0.3 + 25j, 0.8 + 40j)]
confere('Q: |zeta(1-s)|/|zeta(s)| finito e nao nulo (fator chi da equacao funcional)',
        all(0 < r < 1e3 for r in razoes), ', '.join(f'{r:.4f}' for r in razoes))

# ---------- 7. Dual: zero com w != 0 exige zeta'(rho) = 0 ----------
for g in (g1, g2):
    d1 = derivadas(0.5 + 1j * g, 1)[1]
    confere(f"Dual: zeta'(1/2 + i {g:.4f}) != 0, logo so w = 0 (conjectura dos zeros simples, nao RH)",
            abs(d1) > 0.5, f'{d1.real:.5f} {d1.imag:+.5f}i')

print()
print(f'{len(falhas)} falha(s)')
sys.exit(1 if falhas else 0)
