"""As caudas em frações, os zeros em frações e como zeros fora da reta puxariam as caudas.

    python3 caudas_fracoes.py pasta_c1 pasta_c2      (grava caudas_fracoes.json, zeros_em_fracoes.csv, puxao.json)

Dados: os 14 380 683 zeros contíguos certificados (Arb, bolas ≤ 5,01·10⁻¹⁸, todos em Re s = ½, déficit 0).

1. Caudas em frações exatas: quantos espaçamentos normalizados s ficam abaixo de x (cauda curta, quase-encontros) e
   acima de x (cauda longa, vazios), como fração reduzida contagem/total e "1 em k".
2. Zeros em frações: a parte depois da vírgula ("a cauda" do número) de cada zero dos lugares mais apertados, como
   fração exata do centro da bola (p/10^k reduzida) e como a fração mais simples que cabe na bola certificada
   [c − r, c + r] (o zero está nela). Idem para a distância Δγ de cada par mais próximo.
3. O puxão (modelo do par isolado, fluxo de de Bruijn para trás, t < 0): no tempo t sai da reta todo par com
   Δγ² < −2t, a b(t) = √(−Δγ² − 2t)/2 de Re s = ½. Na reta, o vizinho da esquerda, o par e o da direita viram um
   espaço só. Medimos como isso come a cauda curta e engorda a cauda longa. Não é ζ (em t = 0 nada saiu da reta).
"""
import csv
import gzip
import json
import math
import sys
from decimal import Decimal
from fractions import Fraction
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
s = gaps / delta
NG = len(s)


def fr(cont, tot):
    f = Fraction(int(cont), int(tot))
    return {"fracao": f"{f.numerator}/{f.denominator}", "contagem": int(cont), "total": int(tot),
            "um_em": (round(tot / cont) if cont else None)}


# 1. caudas
curta = []
for x in [Fraction(1, 1000), Fraction(1, 400), Fraction(1, 300), Fraction(1, 200), Fraction(1, 100), Fraction(1, 50),
          Fraction(1, 20), Fraction(1, 10), Fraction(1, 5), Fraction(1, 2), Fraction(1)]:
    c = int((s < float(x)).sum())
    curta.append({"s_menor_que": f"{x.numerator}/{x.denominator}", **fr(c, NG)})
longa = []
for x in [Fraction(2), Fraction(5, 2), Fraction(3), Fraction(13, 4), Fraction(7, 2), Fraction(18, 5)]:
    c = int((s > float(x)).sum())
    longa.append({"s_maior_que": f"{x.numerator}/{x.denominator}", **fr(c, NG)})


# 2. zeros em frações
def mais_simples(a, b):
    """A fração de menor denominador em [a, b] (0 ≤ a < b)."""
    fa = a.numerator // a.denominator
    if Fraction(fa) == a:
        return Fraction(fa)
    if fa + 1 <= b:
        return Fraction(fa + 1)
    return fa + 1 / mais_simples(1 / (b - fa), 1 / (a - fa))


def em_fracao(k):
    c = Fraction(Decimal(tt[k]))
    r = Fraction(Decimal(rr[k]))
    inteiro = c.numerator // c.denominator
    cauda = c - inteiro
    simples = mais_simples(cauda - r, cauda + r)
    return {"indice": int(idx[k]), "t": tt[k], "raio": rr[k], "parte_inteira": inteiro,
            "cauda_do_centro": f"{cauda.numerator}/{cauda.denominator}",
            "cauda_mais_simples_na_bola": f"{simples.numerator}/{simples.denominator}",
            "erro_da_fracao_simples": float(abs(simples - cauda))}


ordem = np.argsort(gaps)
lugares = []
usados = set()
for k in ordem[:8]:
    k = int(k)
    viz = list(range(max(0, k - 3), min(len(h), k + 5)))
    dg = Fraction(Decimal(tt[k + 1])) - Fraction(Decimal(tt[k]))
    erro = Fraction(Decimal(rr[k])) + Fraction(Decimal(rr[k + 1]))
    simples = mais_simples(dg - erro, dg + erro)
    lugares.append({"tipo": "par mais próximo", "zeros": [em_fracao(j) for j in viz], "par": [int(idx[k]), int(idx[k + 1])],
                    "Delta_gamma_exato_dos_centros": f"{dg.numerator}/{dg.denominator}",
                    "Delta_gamma_fracao_mais_simples": f"{simples.numerator}/{simples.denominator}",
                    "s": float(s[k]), "s_vizinhos": [float(s[k - 1]), float(s[k + 1])]})
span7 = h[6:] - h[:-6]
k = int(np.argmin(span7))
lugares.append({"tipo": "aglomeração mais densa (7 zeros)", "zeros": [em_fracao(j) for j in range(k - 2, k + 9)],
                "trecho_em_espacamentos": float(span7[k] / delta)})
k = int(np.argmax(gaps))
lugares.append({"tipo": "maior vazio", "zeros": [em_fracao(j) for j in range(k - 2, k + 4)], "s": float(s[k])})

# 3. o puxão
puxao = []
for t in [-1e-7, -2e-7, -5e-7, -1e-6, -1e-5, -1e-4, -1e-3]:
    fora = np.nonzero(gaps ** 2 < -2 * t)[0]
    fora = fora[(fora > 0) & (fora < NG - 1)]
    b = np.sqrt(-gaps[fora] ** 2 - 2 * t) / 2
    rem = np.zeros(NG, bool)
    rem[fora] = rem[fora - 1] = rem[fora + 1] = True
    fundidos = (gaps[fora - 1] + gaps[fora] + gaps[fora + 1]) / delta
    novo = np.concatenate([s[~rem], fundidos])
    puxao.append({
        "t": t, "pares_fora_da_reta": int(len(fora)), "fracao_dos_pares": fr(len(fora), NG)["fracao"],
        "b_max": float(b.max()) if len(b) else 0.0, "b_mediano": float(np.median(b)) if len(b) else 0.0,
        "menor_s_na_reta": float(novo.min()),
        "cauda_curta_s<1/100": fr(int((novo < 0.01).sum()), len(novo)),
        "cauda_longa_s>3": fr(int((novo > 3).sum()), len(novo)),
        "cauda_longa_s>7/2": fr(int((novo > 3.5).sum()), len(novo)),
        "espaco_criado_medio": float(fundidos.mean()) if len(fundidos) else None,
    })
json.dump({"zeros": len(h), "espacamentos": NG, "cauda_curta": curta, "cauda_longa": longa, "lugares": lugares},
          open("caudas_fracoes.json", "w"), ensure_ascii=False, indent=1)
json.dump(puxao, open("puxao.json", "w"), ensure_ascii=False, indent=1)
with open("zeros_em_fracoes.csv", "w", newline="") as f:
    w = csv.writer(f)
    w.writerow(["lugar", "indice", "t_centro_da_bola", "raio", "parte_inteira", "cauda_do_centro_fracao_exata",
                "cauda_fracao_mais_simples_na_bola"])
    for L in lugares:
        for z in L["zeros"]:
            w.writerow([L["tipo"], z["indice"], z["t"], z["raio"], z["parte_inteira"], z["cauda_do_centro"],
                        z["cauda_mais_simples_na_bola"]])
# série fina para a figura do puxão
serie = []
for t in -np.logspace(-8, -3, 41):
    fora = np.nonzero(gaps ** 2 < -2 * t)[0]
    serie.append({"t": float(t), "pares": int(len(fora)),
                  "b_max": float(np.sqrt(-gaps[fora].min() ** 2 - 2 * t) / 2) if len(fora) else 0.0})
json.dump({"serie": serie}, open("puxao_serie.json", "w"))
print(json.dumps({"curta": curta, "longa": longa}, ensure_ascii=False)[:3000])
print(json.dumps(puxao, ensure_ascii=False)[:3000])
