"""As duas refutações indiretas conferidas até N: Chebyshev ψ(x) (forma explícita de Schoenfeld) e Mertens M(x).

    python3 psi_mertens.py [N]      (padrão N = 10^8)

* von Koch / Schoenfeld (1976, Math. Comp. 30): com RH, |ψ(x) − x| < √x·log²x/(8π) para x ≥ 73,2; e uma cota assim
  para todo x dá ψ(x) − x = O(x^{1/2+ε}), que dá RH. Um único x ≥ 73,2 com |ψ(x) − x| ≥ √x·log²x/(8π) refutaria RH.
  ψ é constante entre potências de primos e x − ψ cresce linearmente, então o máximo de |ψ(x) − x| em cada intervalo
  [q_i, q_{i+1}) está nas pontas: confere-se ψ_i − q_i e q_{i+1} − ψ_i contra a cota em q_i (a cota cresce em x).
* Littlewood: RH ⟺ M(x) = O(x^{1/2+ε}) para todo ε > 0. A conjectura de Mertens (|M(x)| ≤ √x) é falsa (Odlyzko–te
  Riele, 1985) sem que se conheça um x explícito, e isso não refuta RH. Aqui: o máximo de |M(x)|/√x até N.

Grava resultados/psi_mertens.json. Nada aqui prova RH.
"""
import json
import math
import sys
from pathlib import Path

import numpy as np

N = int(float(sys.argv[1])) if len(sys.argv) > 1 else 10 ** 8
AQUI = Path(__file__).resolve().parent

crivo = np.ones(N + 1, dtype=bool)
crivo[:2] = False
for p in range(2, int(N ** 0.5) + 1):
    if crivo[p]:
        crivo[p * p::p] = False
primos = np.nonzero(crivo)[0]
del crivo

# ψ: potências de primos ordenadas, com log p
qs, ls = [primos.astype(np.int64)], [np.log(primos.astype(np.float64))]
pk = primos[primos <= int(N ** 0.5)].astype(np.int64)
base = pk.copy()
while len(pk):
    pk = pk * base[:len(pk)]
    ok = pk <= N
    pk, base = pk[ok], base[:len(pk)][ok]
    if len(pk):
        qs.append(pk)
        ls.append(np.log(base.astype(np.float64)))
q = np.concatenate(qs)
lg = np.concatenate(ls)
o = np.argsort(q, kind="stable")
q, lg = q[o], lg[o]
psi = np.cumsum(lg)  # ψ(x) para q_i ≤ x < q_{i+1}
qf = q.astype(np.float64)
prox = np.append(qf[1:], float(N) + 1.0)
m = qf >= 74
desvio = np.maximum(np.abs(psi - qf), np.abs(prox - psi))
cota = np.sqrt(qf) * np.log(qf) ** 2 / (8 * math.pi)
razao = desvio[m] / (np.sqrt(qf[m]) * np.log(qf[m]) ** 2)
i_max = int(np.argmax(razao))
res_psi = {"potencias_de_primos": int(len(q)), "violacoes_schoenfeld_x_ge_74": int((desvio[m] >= cota[m]).sum()),
           "max_desvio_sobre_raiz_x_log2_x": float(razao[i_max]), "em_x": int(q[m][i_max]),
           "limite_schoenfeld": 1 / (8 * math.pi),
           "max_desvio_sobre_raiz_x": float(np.max(desvio[m] / np.sqrt(qf[m])))}
del q, lg, psi, qf, prox, desvio, cota, razao

# μ por crivo e M(x)
mu = np.ones(N + 1, dtype=np.int8)
mu[0] = 0
for p in primos:
    mu[p::p] *= -1
    pp = int(p) * int(p)
    if pp <= N:
        mu[pp::pp] = 0
M = np.cumsum(mu[1:], dtype=np.int32)
x = np.arange(1, N + 1, dtype=np.float64)
r = np.abs(M) / np.sqrt(x)
j = int(np.argmax(r[199:])) + 199  # a partir de x = 200
res_M = {"max_abs_M_sobre_raiz_x_x_ge_200": float(r[j]), "em_x": j + 1, "M_la": int(M[j]),
         "max_abs_M": int(np.max(np.abs(M))), "M_N": int(M[-1])}
res = {"N": N, "psi_schoenfeld": res_psi, "mertens": res_M}
(AQUI / "resultados").mkdir(exist_ok=True)
(AQUI / "resultados" / "psi_mertens.json").write_text(json.dumps(res, ensure_ascii=False, indent=1))
print(json.dumps(res, ensure_ascii=False, indent=1))
