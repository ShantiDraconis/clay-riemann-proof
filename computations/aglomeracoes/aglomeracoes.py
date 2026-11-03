"""Aglomerações e vazios nos 2 054 383 zeros da continuação contígua (seção 31), com S(t) e o par mais frágil de cada.

    python3 aglomeracoes.py pasta_com_zeros{0..3}.csv.gz > aglomeracoes.json

Janela de W = 4 espaçamentos médios (≈ 0,9346 em t) a partir de cada zero: a contagem esperada é 4. Uma aglomeração
é uma janela com muito mais zeros; um vazio é um espaçamento muito maior que o médio. Para cada aglomeração: altura,
contagem, o par mais próximo dentro dela, o `λ ≈ −Δγ²/2` do par (coordenadas x = 2γ) e S(t) logo depois de cada
zero (θ(t)/π pela expansão de Taylor em C0, como em continuacao/gram.py). Fora do kernel.
"""
import gzip
import json
import math
import sys
from decimal import Decimal

import numpy as np

sys.path.insert(0, "/home/claude/ext/mpmath")
from mpmath import mp, mpf, siegeltheta, pi, log, floor

mp.dps = 50
pasta = sys.argv[1]
C0, N0 = "3000175342471.5", 12363153478531
rows = []
for I in range(4):
    rows += [l.strip().split(",") for l in gzip.open(f"{pasta}/zeros{I}.csv.gz", "rt")][1:]
idx = np.array([int(r[0]) for r in rows], dtype=np.int64)
h = np.array([float(Decimal(r[1]) - Decimal(C0)) for r in rows])
t0 = mpf(C0)
th0 = siegeltheta(t0) / pi
A = int(floor(th0))
B, C = float(log(t0 / (2 * pi)) / 2 / pi), float(1 / (4 * pi * t0))
S_dep = (idx - A) - (float(th0 - A) + B * h + C * h * h) - 1
delta = 2 * math.pi / math.log(3.0001755e12 / (2 * math.pi))
W = 4 * delta
fim = np.searchsorted(h, h + W, side="left")
cont = fim - np.arange(len(h))           # zeros em [γ_k, γ_k + W)
gaps = np.diff(h)


def nao_sobrepostos(ordem, largura, n):
    usados, sel = np.zeros(len(h), bool), []
    for k in ordem:
        if usados[k:k + largura].any():
            continue
        sel.append(int(k))
        usados[max(0, k - largura):k + largura] = True
        if len(sel) == n:
            break
    return sel


# as aglomerações mais densas: 7 zeros seguidos no menor trecho de altura (a contagem máxima em W é 7)
span7 = h[6:] - h[:-6]
aglom = []
for k in nao_sobrepostos(np.argsort(span7, kind="stable"), 12, 12):
    j = k + 7
    g = gaps[k:j - 1]
    m = k + int(np.argmin(g))
    dg = float(gaps[m])
    aglom.append({
        "zero_inicial": int(idx[k]), "t_inicial": rows[k][1], "zeros_em_4_espacamentos": int(cont[k]),
        "esperado": 4, "t_rel_C0": float(h[k]), "trecho_de_7_zeros": float(span7[k]),
        "trecho_em_espacamentos": float(span7[k] / delta),
        "zeros": [{"indice": int(idx[i]), "t_rel": float(h[i] - h[k]), "S_depois": round(float(S_dep[i]), 4)}
                  for i in range(max(0, k - 3), min(len(h), j + 3))],
        "par_mais_proximo": [int(idx[m]), int(idx[m + 1])], "Delta_gamma": dg, "s": dg / delta,
        "lambda_colisao": -dg * dg / 2,
    })
vazios = []
for k in nao_sobrepostos(np.argsort(-gaps, kind="stable"), 4, 8):
    vazios.append({"entre_zeros": [int(idx[k]), int(idx[k + 1])], "t_rel_C0": float(h[k]),
                   "Delta_gamma": float(gaps[k]), "s": float(gaps[k] / delta),
                   "S_antes": round(float(S_dep[k]), 4), "S_no_fim": round(float(S_dep[k] - gaps[k] / delta), 4)})
hist = np.bincount(cont, minlength=int(cont.max()) + 1)
# excesso por bloco de 2000 zeros: máximo de contagem no bloco (para o gráfico ao longo da altura)
bl = 2000
perfil = [{"t_rel_C0": float(h[i]), "max_contagem": int(cont[i:i + bl].max()), "min_espacamento_s":
           float(gaps[i:i + bl - 1].min() / delta)} for i in range(0, len(h) - bl, bl)]
print(json.dumps({"C0": C0, "espacamento_medio": delta, "janela_W": W, "zeros": len(h),
                  "distribuicao_contagem_em_W": {str(i): int(v) for i, v in enumerate(hist) if v},
                  "aglomeracoes": aglom, "vazios": vazios, "perfil": perfil}, ensure_ascii=False))
