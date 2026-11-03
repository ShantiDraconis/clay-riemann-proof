"""Os locais exatos dos quase-encontros e das aglomerações nos 14 380 683 zeros contíguos certificados.

    python3 locais_exatos.py pasta_c1 pasta_c2 > locais_exatos.json   (e grava locais_exatos.csv)

Cada zero sai como a bola da Arb [t ± r] (r ≤ 5,01·10⁻¹⁸) com Re s = ½. Listas:
* os 20 pares mais próximos (Δγ = distância entre os centros, com o erro r₁ + r₂);
* as 15 aglomerações mais densas: 7 zeros seguidos no menor trecho de altura (contagem máxima numa janela de
  4 espaçamentos médios, conferida na lista inteira);
* os 10 maiores vazios.
"""
import csv
import gzip
import json
import math
import sys
from decimal import Decimal
from pathlib import Path

import numpy as np

C0 = Decimal("3000175342471.5")
idx, h, tt, rr = [], [], [], []
for pasta, faixas in ((sys.argv[1], range(4)), (sys.argv[2], range(24))):
    for I in faixas:
        for linha in gzip.open(Path(pasta) / f"zeros{I}.csv.gz", "rt"):
            if linha.startswith("indice"):
                continue
            i, m, r = linha.strip().split(",")
            idx.append(int(i)); tt.append(m); rr.append(r); h.append(float(Decimal(m) - C0))
idx = np.array(idx, dtype=np.int64)
h = np.array(h)
delta = 2 * math.pi / math.log(3.000177e12 / (2 * math.pi))
gaps = np.diff(h)
W = 4 * delta
cont = np.searchsorted(h, h + W, side="left") - np.arange(len(h))
span7 = h[6:] - h[:-6]


def sel(ordem, largura, n):
    usados, out = np.zeros(len(h), bool), []
    for k in ordem:
        k = int(k)
        if usados[max(0, k - largura):k + largura].any():
            continue
        out.append(k)
        usados[max(0, k - largura):k + largura] = True
        if len(out) == n:
            break
    return out


def zero(k):
    return {"indice": int(idx[k]), "t": tt[k], "raio": rr[k]}


pares = []
for k in sel(np.argsort(gaps), 2, 20):
    erro = float(Decimal(rr[k]) + Decimal(rr[k + 1]))
    pares.append({"zeros": [zero(k), zero(k + 1)], "Delta_gamma": str(Decimal(tt[k + 1]) - Decimal(tt[k])),
                  "erro_Delta_gamma": erro, "s": float(gaps[k] / delta), "lambda": -float(gaps[k]) ** 2 / 2})
aglom = []
for k in sel(np.argsort(span7), 12, 15):
    g = gaps[k:k + 6]
    aglom.append({"zeros": [zero(i) for i in range(k, k + 7)], "trecho": float(span7[k]),
                  "trecho_em_espacamentos": float(span7[k] / delta), "menor_s_dentro": float(g.min() / delta)})
vazios = []
for k in sel(np.argsort(-gaps), 2, 10):
    vazios.append({"zeros": [zero(k), zero(k + 1)], "Delta_gamma": float(gaps[k]), "s": float(gaps[k] / delta)})
out = {"zeros": len(h), "espacamento_medio": delta, "maior_contagem_em_4_espacamentos": int(cont.max()),
       "janelas_com_a_maior_contagem": int((cont == cont.max()).sum()),
       "distribuicao_contagem": {str(i): int(v) for i, v in enumerate(np.bincount(cont)) if v},
       "pares_mais_proximos": pares, "aglomeracoes_mais_densas": aglom, "maiores_vazios": vazios}
print(json.dumps(out, ensure_ascii=False, indent=1))
with open("locais_exatos.csv", "w", newline="") as f:
    w = csv.writer(f)
    w.writerow(["tipo", "ordem", "indice", "t_centro_da_bola", "raio", "s_do_grupo"])
    for j, p in enumerate(pares, 1):
        for z in p["zeros"]:
            w.writerow(["par", j, z["indice"], z["t"], z["raio"], f"{p['s']:.6f}"])
    for j, a in enumerate(aglom, 1):
        for z in a["zeros"]:
            w.writerow(["aglomeracao_7_zeros", j, z["indice"], z["t"], z["raio"], f"{a['trecho_em_espacamentos']:.4f}"])
    for j, v in enumerate(vazios, 1):
        for z in v["zeros"]:
            w.writerow(["vazio", j, z["indice"], z["t"], z["raio"], f"{v['s']:.4f}"])
