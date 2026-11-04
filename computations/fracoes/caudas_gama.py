"""As caudas das partes imaginárias em frações: o que elas compartilham.

    python3 caudas_gama.py pasta_c1 pasta_c2 > caudas_gama.json

Dados: os 14 380 683 zeros contíguos certificados (Arb) com 3 000 175 342 471,5 < γ ≤ 3 000 178 702 471,5, cada um
uma bola [c − r, c + r], r ≤ 5,01·10⁻¹⁸, c com 17 casas.

1. A cauda {γ} (a parte depois da vírgula) como fração exata p/10¹⁷. Equidistribuição (Hlawka 1975: {αγ_n} é
   equidistribuída para todo α ≠ 0): histograma em 100 caixas, qui-quadrado, distância de Kolmogorov–Smirnov.
2. A fração contínua da cauda, só os quocientes parciais que a bola certifica (prefixo comum das frações contínuas de
   c − r e c + r). Comparação com Gauss–Kuzmin P(a = k) = log₂(1 + 1/(k(k + 2))), com a constante de Khinchin
   K₀ = 2,685452… e a de Lévy e^{π²/(12 ln 2)} = 3,275822… (as de quase todo número real).
3. A fração mais simples dentro da bola (Stern–Brocot): o tamanho do denominador (~ 1/√(largura da bola)).
Amostra para 2 e 3: 1 000 000 de zeros (amostragem por reservatório, semente 2026).
"""
import gzip
from array import array
import json
import math
import random
import sys
from fractions import Fraction
from multiprocessing import Pool
from pathlib import Path

import numpy as np

random.seed(2026)
TAM = 1_000_000
fr_l = array("d")
amostra_l = []
N = 0
for pasta, faixas in ((sys.argv[1], range(4)), (sys.argv[2], range(24))):
    for I in faixas:
        for linha in gzip.open(Path(pasta) / f"zeros{I}.csv.gz", "rt"):
            if linha.startswith("indice"):
                continue
            i, m, r = linha.strip().split(",")
            fr_l.append(float("0." + m.split(".")[1][:15]))
            # amostragem por reservatório (algoritmo R), semente fixa
            if N < TAM:
                amostra_l.append((m, r))
            else:
                j = random.randrange(N + 1)
                if j < TAM:
                    amostra_l[j] = (m, r)
            N += 1
fr = np.frombuffer(fr_l, dtype=float)
# 1. equidistribuição
cont, _ = np.histogram(fr, bins=100, range=(0, 1))
esp = N / 100
qui2 = float(((cont - esp) ** 2 / esp).sum())
fs = np.sort(fr)
ks = float(np.max(np.maximum(np.arange(1, N + 1) / N - fs, fs - np.arange(N) / N)))


def cf(fr_, nmax=40):
    a = []
    x = fr_
    for _ in range(nmax):
        q = x.numerator // x.denominator
        a.append(q)
        x = x - q
        if x == 0:
            break
        x = 1 / x
    return a


def certificado(arg):
    m, r = arg
    inteiro, dec = m.split(".")
    c = Fraction(int(dec), 10 ** len(dec))
    rr = Fraction(r) if "E" not in r else Fraction(float(r)).limit_denominator(10 ** 30)
    rr = Fraction(Decimal_to_fraction(r))
    a1, a2 = cf(c - rr), cf(c + rr)
    pref = []
    for x, y in zip(a1, a2):
        if x != y:
            break
        pref.append(x)
    # fração mais simples em [c − r, c + r] (Stern–Brocot pelo prefixo)
    lo, hi = c - rr, c + rr
    p0, q0, p1, q1 = 0, 1, 1, 0
    for k in pref:
        p0, q0, p1, q1 = p1, q1, k * p1 + p0, k * q1 + q0
    # próximo passo: menor k com a convergente dentro do intervalo
    x, y = (cf(lo), cf(hi))
    j = len(pref)
    kmin = min(x[j], y[j]) + 1 if j < len(x) and j < len(y) else 1
    p, q = kmin * p1 + p0, kmin * q1 + q0
    simples = Fraction(p, q)
    if not (lo <= simples <= hi):
        simples = Fraction(p1, q1)
    return pref[1:], simples.denominator, float(2 * rr)


def Decimal_to_fraction(s):
    from decimal import Decimal
    return Fraction(Decimal(s))


with Pool(2) as pool:
    res = pool.map(certificado, amostra_l, chunksize=5000)
contagem = {}
khin_log, khin_n = 0.0, 0
levy = []
comp = []
dens = []
for pref, qd, larg in res:
    comp.append(len(pref))
    dens.append(qd)
    for a in pref[:12]:
        if a >= 1:
            contagem[a] = contagem.get(a, 0) + 1
            khin_log += math.log(a)
            khin_n += 1
    # Lévy: log q_n / n no último convergente certificado
    p0, q0, p1, q1 = 0, 1, 1, 0
    for a in pref:
        p0, q0, p1, q1 = p1, q1, a * p1 + p0, a * q1 + q0
    if len(pref) >= 8:
        levy.append(math.log(q1) / len(pref))
tot = sum(contagem.values())
gk = [{"k": k, "observado": contagem.get(k, 0) / tot, "gauss_kuzmin": math.log2(1 + 1 / (k * (k + 2)))}
      for k in range(1, 21)]
ld = np.log10(np.array(dens, dtype=float))
print(json.dumps({
    "zeros": N,
    "equidistribuicao": {"caixas": 100, "qui2": qui2, "graus_de_liberdade": 99, "ks": ks,
                         "ks_vezes_raiz_N": ks * math.sqrt(N), "contagens": cont.tolist()},
    "fracao_continua": {"amostra": len(res), "quocientes_certificados_media": float(np.mean(comp)),
                        "quocientes_certificados_min": int(np.min(comp)), "quocientes_certificados_max": int(np.max(comp)),
                        "gauss_kuzmin": gk, "khinchin_observado": math.exp(khin_log / khin_n),
                        "khinchin_teorico": 2.6854520010653064, "levy_observado": math.exp(float(np.mean(levy))),
                        "levy_teorico": math.exp(math.pi ** 2 / (12 * math.log(2)))},
    "fracao_mais_simples_na_bola": {"log10_denominador_mediana": float(np.median(ld)),
                                    "log10_denominador_p05": float(np.percentile(ld, 5)),
                                    "log10_denominador_p95": float(np.percentile(ld, 95)),
                                    "previsao_1_sobre_raiz_largura_log10": float(-0.5 * np.log10(np.median([r[2] for r in res])))}
}, ensure_ascii=False))
