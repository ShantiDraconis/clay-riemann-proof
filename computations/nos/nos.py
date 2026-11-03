"""Todos os nós suspeitos de uma lista certificada de zeros: aglomerações, vazios, Rosser, S(t) extremo e pares frágeis.

    python3 nos.py ZEROS.csv.gz SAIDA.json [ROTULO] [MAX_NOS]

Um nó é um trecho curto de alturas em que os zeros fogem do comportamento típico. Tipos:

* **aglomeração / vazio**: excesso ou falta de zeros numa janela de L espaçamentos médios (L = 2, 5, 10, 25),
  medido contra a variância de número do GUE, Σ²(L) ≈ (log(2πL) + γ + 1 − π²/8)/π² (é a variação de S(t) na janela);
* **Gram triplo**: um intervalo de Gram com 3 ou mais zeros;
* **Rosser**: um bloco de Gram de k intervalos sem k zeros;
* **S extremo**: |S(t)| além de 4 desvios de Selberg (variância log log T / (2π²));
* **par frágil**: espaçamento normalizado s < 0,08 (onde o fluxo de de Bruijn faria a colisão).

Cada nó sai com o intervalo de índices e de alturas, os tipos e uma nota (maior desvio em σ). A lista vai para
`ataca_nos.py`, que recalcula os zeros do nó com a Arb e faz a contagem de Turing local. Fora do kernel.
"""
import bisect
import gzip
import json
import math
import sys
from decimal import Decimal, getcontext

getcontext().prec = 60
ENT, SAI = sys.argv[1], sys.argv[2]
ROTULO = sys.argv[3] if len(sys.argv) > 3 else ENT
MAX = int(sys.argv[4]) if len(sys.argv) > 4 else 60
PI = Decimal("3.14159265358979323846264338327950288419716939937510582097494459230781640628620899")
EULER = 0.5772156649015329

L = [l.strip().split(",") for l in gzip.open(ENT, "rt")][1:]
idx = [int(r[0]) for r in L]
gam = [Decimal(r[1]) for r in L]
n = len(gam)


def theta(t):
    return (t / 2) * (t / (2 * PI)).ln() - t / 2 - PI / 8 + 1 / (48 * t) + Decimal(7) / (5760 * t ** 3)


T = float(gam[n // 2])
rho = math.log(T / (2 * math.pi)) / (2 * math.pi)
rel = [float(g - gam[0]) for g in gam]
u = [r * rho for r in rel]  # alturas desdobradas (espaçamento médio 1)
S = [float(idx[i] - theta(gam[i]) / PI - 1) for i in range(n)]  # S logo depois de cada zero
sd_S = math.sqrt(math.log(math.log(T)) / (2 * math.pi ** 2))
nos = []


def no(i0, i1, tipo, nota, detalhe):
    nos.append({"i0": max(i0, 0), "i1": min(i1, n - 1), "tipo": tipo, "nota": nota, "detalhe": detalhe})


# aglomerações e vazios: janela [u_i, u_i + L)
for Lw in (2, 5, 10, 25):
    sig = math.sqrt(max((math.log(2 * math.pi * Lw) + EULER + 1 - math.pi ** 2 / 8) / math.pi ** 2, 1e-9))
    j = 0
    melhor = []
    for i in range(n):
        if u[i] + Lw > u[-1]:
            break  # janela passaria do último zero da lista
        while j < n and u[j] < u[i] + Lw:
            j += 1
        c = j - i  # zeros em [u_i, u_i + L)
        z = (c - Lw) / sig
        melhor.append((z, i, j - 1, c))
    melhor.sort()
    for z, i, jj, c in melhor[-12:]:
        no(i, jj, f"aglomeração L={Lw}", z, f"{c} zeros onde se esperam {Lw} (Σ = {sig:.3f})")
    for z, i, jj, c in melhor[:6]:
        no(i, jj, f"vazio L={Lw}", -z, f"{c} zeros onde se esperam {Lw} (Σ = {sig:.3f})")
# pontos de Gram: intervalos com 3+ zeros e violações de Rosser
m0 = int((theta(gam[0]) / PI).to_integral_value(rounding="ROUND_CEILING"))
m1 = int((theta(gam[-1]) / PI).to_integral_value(rounding="ROUND_FLOOR"))
gp = []
t = gam[0]
for m in range(m0, m1 + 1):
    for _ in range(60):
        t2 = t - (theta(t) - m * PI) / ((t / (2 * PI)).ln() / 2)
        if abs(t2 - t) < Decimal("1e-30"):
            t = t2
            break
        t = t2
    gp.append((m, t))


def N(tt):
    jj = bisect.bisect_right(gam, tt) - 1
    return idx[0] - 1 if jj < 0 else idx[jj]


Ng = [N(g) for _, g in gp]
for k in range(len(gp) - 1):
    c = Ng[k + 1] - Ng[k]
    if c >= 3:
        i0 = Ng[k] - idx[0] + 1
        no(i0, i0 + c - 1, "Gram triplo", c, f"{c} zeros em [g_{gp[k][0]}, g_{gp[k][0] + 1})")
bons = [k for k in range(len(gp)) if (Ng[k] - gp[k][0] - 1) % 2 == 0]
for a, b in zip(bons, bons[1:]):
    if Ng[b] - Ng[a] != b - a:
        i0 = Ng[a] - idx[0] + 1
        no(i0 - 1, i0 + max(Ng[b] - Ng[a], 1), "Rosser", 6.0,
           f"bloco de {b - a} intervalos com {Ng[b] - Ng[a]} zeros (g_{gp[a][0]})")
# S extremo e pares frágeis
for i in range(n):
    if abs(S[i]) > 4 * sd_S or abs(S[i] - 1) > 4 * sd_S and S[i] - 1 < 0:
        z = max(abs(S[i]), abs(S[i] - 1)) / sd_S
        no(i - 2, i + 2, "S extremo", z, f"S = {S[i]:.3f} logo depois do zero (−{1 - S[i]:.3f} antes)")
for i in range(n - 1):
    s = u[i + 1] - u[i]
    if s < 0.08:
        no(i - 1, i + 2, "par frágil", 0.08 / s, f"s = {s:.4f}")

# junta nós sobrepostos
nos.sort(key=lambda x: x["i0"])
juntos = []
for x in nos:
    if juntos and x["i0"] <= juntos[-1]["i1"] + 2:
        y = juntos[-1]
        y["i1"] = max(y["i1"], x["i1"])
        y["tipos"].add(x["tipo"].split(" L=")[0])
        y["notas"].append(x["nota"])
        y["detalhes"].append(f"{x['tipo']}: {x['detalhe']}")
    else:
        juntos.append({"i0": x["i0"], "i1": x["i1"], "tipos": {x["tipo"].split(" L=")[0]}, "notas": [x["nota"]],
                       "detalhes": [f"{x['tipo']}: {x['detalhe']}"]})
for y in juntos:
    y["pontos"] = len(y["tipos"]) * 2 + max(y["notas"])
    y["tipos"] = sorted(y["tipos"])
    y["indice_inicio"], y["indice_fim"] = idx[y["i0"]], idx[y["i1"]]
    y["t_inicio"], y["t_fim"] = str(gam[y["i0"]]), str(gam[y["i1"]])
    y["S_max_no"] = max(S[y["i0"]:y["i1"] + 1])
    del y["notas"]
juntos.sort(key=lambda y: -y["pontos"])
out = {"rotulo": ROTULO, "zeros": n, "altura": T, "desvio_S_selberg": sd_S, "nos": juntos[:MAX],
       "contagem_por_tipo": {t: sum(1 for y in juntos if t in y["tipos"]) for t in
                             ("aglomeração", "vazio", "Gram triplo", "Rosser", "S extremo", "par frágil")}}
json.dump(out, open(SAI, "w"), ensure_ascii=False, indent=1)
print(json.dumps(out["contagem_por_tipo"], ensure_ascii=False))
for y in juntos[:20]:
    print(f"{y['pontos']:6.2f} {y['indice_inicio']}–{y['indice_fim']} t={y['t_inicio'][:22]}…{y['t_fim'][14:22]} "
          f"{'/'.join(y['tipos'])} | {'; '.join(y['detalhes'][:3])[:150]}")
