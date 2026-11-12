#!/usr/bin/env python3
"""Testes numéricos do "eixo Riemann", espelhando ClayRiemannProof/EixoRiemann/Algebra.lean.

R3:   a + b i + c R com i² = -1, R² = R, i·R = R·i = R  (3 componentes reais, tabuada proposta)
Dual: z + w ε com ε² = 0                                  (4 componentes reais)
Idem: z + w e com e² = e                                  (4 componentes reais)

Uso: python3 test_eixo.py   (sai com código 0 se todos os testes passam)
"""
import random
import sys


def r3_mul(x, y):
    a, b, c = x
    d, e, f = y
    return (a * d - b * e, a * e + b * d, a * f + c * d + c * f + b * f + c * e)


def dual_mul(x, y):
    return (x[0] * y[0], x[0] * y[1] + x[1] * y[0])


def idem_mul(x, y):
    return (x[0] * y[0], x[0] * y[1] + x[1] * y[0] + x[1] * y[1])


def perto(u, v, tol=1e-9):
    return all(abs(p - q) <= tol * (1 + abs(p) + abs(q)) for p, q in zip(u, v))


falhas = 0


def confere(nome, cond):
    global falhas
    print(("OK    " if cond else "FALHA ") + nome)
    falhas += 0 if cond else 1


# 1. a tabuada proposta: o exemplo da conversa, comutatividade, unidade
confere("R3: (5+2i+0,1R)(3+i+0,2R) = 13+11i+1,82R", perto(r3_mul((5, 2, 0.1), (3, 1, 0.2)), (13, 11, 1.82)))
rnd = random.Random(20261112)
amostra = [tuple(rnd.uniform(-3, 3) for _ in range(3)) for _ in range(500)]
confere("R3: comutativa em 500 pares", all(perto(r3_mul(x, y), r3_mul(y, x)) for x in amostra for y in amostra[:20]))
confere("R3: 1 é unidade", all(perto(r3_mul((1, 0, 0), x), x) for x in amostra))

# 2. a tabuada proposta não é associativa
i, R = (0, 1, 0), (0, 0, 1)
esq, dir_ = r3_mul(r3_mul(i, i), R), r3_mul(i, r3_mul(i, R))
confere(f"R3: (i·i)·R = {esq} e i·(i·R) = {dir_} são diferentes", not perto(esq, dir_))
trios = [(rnd.choice(amostra), rnd.choice(amostra), rnd.choice(amostra)) for _ in range(2000)]
quebra = sum(not perto(r3_mul(r3_mul(x, y), z), r3_mul(x, r3_mul(y, z))) for x, y, z in trios)
confere(f"R3: associatividade falha em {quebra} de 2000 trios aleatórios", quebra > 0)

# 3. as versões de 4 componentes são associativas
def c():
    return complex(rnd.uniform(-3, 3), rnd.uniform(-3, 3))


for nome, mul in (("Dual (ε²=0)", dual_mul), ("Idem (e²=e)", idem_mul)):
    ok = all(perto(mul(mul(x, y), z), mul(x, mul(y, z)))
             for x, y, z in (((c(), c()), (c(), c()), (c(), c())) for _ in range(2000)))
    confere(f"{nome}: associativa em 2000 trios aleatórios", ok)
confere("Idem: e·e = e", idem_mul((0, 1), (0, 1)) == (0, 1))
confere("Idem: i·e = (0, i), não e", idem_mul((1j, 0), (0, 1)) == (0, 1j))

# 4. Dual faz Taylor de primeira ordem exato: f(z + ε) = f(z) + f'(z) ε, aqui para f(s) = s³ - 2s
def f_dual(x):
    x3 = dual_mul(dual_mul(x, x), x)
    return (x3[0] - 2 * x[0], x3[1] - 2 * x[1])


z0 = 0.6 + 14.1347j
val, der = f_dual((z0, 1))
confere("Dual: derivada de s³ - 2s exata", abs(der - (3 * z0**2 - 2)) < 1e-9)

# 5. a decomposição "puxada" vale também para uma função com zero fora da reta
def puxado(s):
    return complex(0.5, s.imag)


def f(s):
    return s - 1  # zero em s = 1, fora de Re s = 1/2


ok = all(abs(f(s) - (f(puxado(s)) + (f(s) - f(puxado(s))))) < 1e-12 for s in (c() for _ in range(1000)))
confere("decomposição f(s) = f(puxado) + I vale para f(s) = s - 1", ok)
confere("e mesmo assim f tem zero fora da reta (s = 1)", f(1) == 0 and puxado(1).real != 1)

print(f"RESUMO: {falhas} falha(s)")
sys.exit(1 if falhas else 0)
