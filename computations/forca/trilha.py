"""Mudar Z na escala do próprio Z: o caminho dos dois zeros de um par fora da reta, do limiar até b = 0,2 e além.

    python3 trilha.py SAIDA.json PONTOS.json LISTA1.csv.gz [LISTA2.csv.gz ...]

PONTOS.json: lista de {"nome", "gamma_1", "gamma_2"}. Para cada par: o extremo t* da lombada (Newton em Z'), a altura
|Z*| e Z''; depois, para empurrões ε de |Z*| até 30 (a escala do próprio Z: a média quadrática de Z é √log(t/2π) ≈ 5,2
em 3·10¹²), o zero de Z(t* + u) − sinal(Z*)·ε com u complexo, seguido por continuação em ε (Newton a partir do anterior).
O zero em u = δ + iβ é, em s = ½ + it, o ponto ½ − β + i(t* + δ): fora da reta por b = |β|. Com a conjugação e a
equação funcional, o quarteto ½ ± b ± i(t* + δ).

Z(t* + u) para u complexo pequeno: Riemann–Siegel com φ_n(t* + u) = φ_n(t*) + u·k_n, k_n = θ'(t*) − log n (θ'' ≈ 1/2t*
≈ 10⁻¹³ desprezado) e o resto real de t* (varia ≈ 10⁻⁷ por unidade de t). A função empurrada ζ_ε(s) = ζ(s) −
ε·χ(s)^{1/2} tem a mesma equação funcional e a mesma conjugação de ζ, e não tem produto de Euler. Fora do kernel.
"""
import gzip
import json
import math
import sys
from decimal import Decimal, getcontext

import numpy as np

getcontext().prec = 60
SAI, PONTOS, LISTAS = sys.argv[1], sys.argv[2], sys.argv[3:]
PI = Decimal("3.14159265358979323846264338327950288419716939937510582097494459230781640628620899")
DOISPI = 2 * PI


def theta(t):
    return (t / 2) * (t / (2 * PI)).ln() - t / 2 - PI / 8 + 1 / (48 * t) + Decimal(7) / (5760 * t ** 3)


pontos = json.load(open(PONTOS))
T0 = min(int(Decimal(p["gamma_1"])) for p in pontos)
Tmax = max(float(Decimal(p["gamma_2"])) for p in pontos)
NMAX = int(math.sqrt(Tmax / (2 * math.pi))) + 2
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
print("fases prontas", flush=True)


def prepara(T):
    tf = float(T)
    a = math.sqrt(tf / (2 * math.pi))
    N = int(a)
    p = a - N
    phi = float(theta(T) % DOISPI) - fase0[:N] - float(T - T0) * logf[:N]
    k = 0.5 * math.log(tf / (2 * math.pi)) - logf[:N]
    R = (-1) ** (N - 1) * (tf / (2 * math.pi)) ** -0.25 * math.cos(2 * math.pi * (p * p - p - 1 / 16)) / \
        math.cos(2 * math.pi * p)
    return phi, k, amp[:N], R


def Zc(u, pr):
    phi, k, w, R = pr
    arg = phi + u * k
    return 2 * np.dot(w, np.cos(arg)) + R, -2 * np.dot(w * k, np.sin(arg)), -2 * np.dot(w * k * k, np.cos(arg))


res = []
for p in pontos:
    g1, g2 = Decimal(p["gamma_1"]), Decimal(p["gamma_2"])
    T = (g1 + g2) / 2
    pr = prepara(T)
    u = 0.0
    for _ in range(40):  # extremo: Z'(u) = 0
        z, z1, z2 = Zc(u, pr)
        du = -float(np.real(z1)) / float(np.real(z2))
        u += du
        if abs(du) < 1e-14:
            break
    z, z1, z2 = Zc(u, pr)
    a, c2, sig = abs(float(np.real(z))), abs(float(np.real(z2))), (1.0 if float(np.real(z)) > 0 else -1.0)
    ust = u
    # conferência: Z nos dois zeros
    zg1 = abs(float(np.real(Zc(float(g1 - T), pr)[0])))
    zg2 = abs(float(np.real(Zc(float(g2 - T), pr)[0])))
    caminho = []
    eps_lista = [a * (1 + d) for d in (1e-4, 3e-4, 1e-3, 3e-3, 1e-2, 3e-2, 0.1, 0.3, 1, 2, 4)]
    e = eps_lista[-1]
    while e < 30:
        e *= 1.25
        eps_lista.append(e)
    uz = complex(ust, math.sqrt(2 * (eps_lista[0] - a) / c2))
    for eps in eps_lista:
        ok = False
        for _ in range(60):
            g, g1d, _ = Zc(uz, pr)
            g = g - sig * eps
            step = g / g1d
            if abs(step) > 0.05:
                step *= 0.05 / abs(step)
            uz -= step
            if abs(step) < 1e-13:
                ok = True
                break
        b = abs(uz.imag)
        modelo = math.sqrt(2 * (eps - a) / c2)
        caminho.append({"epsilon": eps, "epsilon_relativo": eps / math.sqrt(math.log(float(T) / (2 * math.pi))),
                        "b": b, "deslocamento": uz.real - ust, "b_modelo": modelo, "convergiu": ok})
    alvo = {}
    for bb in (0.001, 0.01, 0.05, 0.1, 0.2):
        for c0, c1 in zip(caminho, caminho[1:]):
            if c0["b"] <= bb <= c1["b"] and c1["b"] > c0["b"]:
                f = (bb - c0["b"]) / (c1["b"] - c0["b"])
                alvo[str(bb)] = c0["epsilon"] + f * (c1["epsilon"] - c0["epsilon"])
                break
    reg = {"nome": p["nome"], "t_estrela": str(T + Decimal(ust)), "forca": a, "Zpp": sig * -c2 if False else -sig * c2,
           "Z_nos_zeros": max(zg1, zg2), "epsilon_para_b": alvo, "caminho": caminho}
    res.append(reg)
    print(p["nome"], f"|Z*|={a:.3e} Z''={-sig * c2:.1f} Z(zeros)={max(zg1, zg2):.1e} ε para b:",
          {k: f"{v:.3g}" for k, v in alvo.items()}, flush=True)
    json.dump(res, open(SAI, "w"), ensure_ascii=False, indent=1)  # a cada ponto: um corte não perde os anteriores
