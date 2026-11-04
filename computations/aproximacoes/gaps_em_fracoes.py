"""Os espaços (gaps) em frações exatas, com a bola certificada, e as sete objeções respondidas com números.

    python3 gaps_em_fracoes.py pasta_c1 pasta_c2      (grava gaps_em_fracoes.json e gaps_em_fracoes.csv)

Dados: os 14 380 683 zeros contíguos (Arb/FLINT 3, método local de Platt, cada zero uma bola [c ± r] em Re s = ½,
contagem de Turing intervalar, déficit 0), de 3 000 175 342 471,5 a 3 000 178 702 471,5.

O centro c de cada bola é um decimal exato, logo uma fração p/10^k. O ZERO NÃO É O CENTRO: só se sabe que está em
[c − r, c + r]. O espaço verdadeiro g = γ_{n+1} − γ_n está em [c_{n+1} − c_n − (r_n + r_{n+1}), … + (r_n + r_{n+1})].
Tudo abaixo que depende do espaço é dado como intervalo que vale para TODO ponto das duas bolas.

1. Média do bloco: a média verdadeira dos espaços é (γ_último − γ_primeiro)/(N − 1) (soma telescópica), não
   comprimento/(N − 1); damos as duas e a média local 2π/log(γ/2π).
2. Os 8 espaços mais curtos e os 3 mais longos: fração exata da diferença dos centros (reduzida, com o mdc), intervalo
   pela bola, fração mais simples no intervalo, s pelas três médias, e λ = −g²/2 (tempo de colisão do par isolado em
   z = 2γ, coordenada do H_t de de Bruijn) como intervalo.
3. As caudas com as duas normalizações (global e local): mudam?
4. A "absorção" Re_abs = ½ + (s − 1)b: com a média verdadeira, Σ s = N − 1 exatamente (telescópica), logo a média de
   Re_abs é ½ para TODO b e TODA sequência: não diz nada sobre os zeros.
5. O mapa do toro θ = 360(s − 1)/(s + 1): monótono em s; onde caem as duas caudas.
"""
import csv
import gzip
import json
import math
import re
import sys
from decimal import Decimal
from fractions import Fraction
from math import gcd
from pathlib import Path

import numpy as np

P1, P2 = Path(sys.argv[1]), Path(sys.argv[2])
arquivos = sorted(P1.glob("zeros*.csv.gz"), key=lambda p: int(re.findall(r"\d+", p.name)[0]))
arquivos += sorted(P2.glob("zeros*.csv.gz"), key=lambda p: int(re.findall(r"\d+", p.name)[0]))
idx, txt, rad = [], [], []
for a in arquivos:
    with gzip.open(a, "rt") as f:
        r = csv.reader(f)
        next(r)
        for linha in r:
            idx.append(int(linha[0]))
            txt.append(linha[1])
            rad.append(linha[2])
N = len(idx)
assert all(b == a + 1 for a, b in zip(idx, idx[1:])), "índices não contíguos"
INF, SUP = Decimal("3000175342471.5"), Decimal("3000178702471.5")
# float de precisão dupla só para ACHAR os candidatos; tudo que vai para o texto é refeito em Fraction
base = Decimal(txt[0].split(".")[0])
x = np.array([float(Decimal(t) - base) for t in txt])
g = np.diff(x)
rmax = max(Decimal(r) for r in rad)


def fr(d):
    return Fraction(Decimal(d))


def reduz(q):
    return {"num": q.numerator, "den": q.denominator}


def bruta(d):
    """Fração p/10^k exatamente como o decimal está escrito, e o mdc com 10^k (prova da redução)."""
    s = str(Decimal(d))
    k = len(s.split(".")[1]) if "." in s else 0
    p = int(s.replace(".", "").replace("-", ""))
    return {"p": p, "10^k": k, "mdc": gcd(p, 10 ** k)}


def mais_simples(lo, hi):
    """A fração de menor denominador em [lo, hi] (Stern–Brocot), 0 < lo < hi."""
    a, b, c, d = 0, 1, 1, 0  # a/b < x < c/d
    while True:
        m = Fraction(a + c, b + d)
        if m < lo:
            a, b = a + c, b + d
            # acelera
            k = 1
            while Fraction(a + k * c, b + k * d) < lo:
                k *= 2
            lo_k, hi_k = 0, k
            while hi_k - lo_k > 1:
                mid = (lo_k + hi_k) // 2
                if Fraction(a + mid * c, b + mid * d) < lo:
                    lo_k = mid
                else:
                    hi_k = mid
            a, b = a + lo_k * c, b + lo_k * d
        elif m > hi:
            c, d = a + c, b + d
            k = 1
            while Fraction(c + k * a, d + k * b) > hi:
                k *= 2
            lo_k, hi_k = 0, k
            while hi_k - lo_k > 1:
                mid = (lo_k + hi_k) // 2
                if Fraction(c + mid * a, d + mid * b) > hi:
                    lo_k = mid
                else:
                    hi_k = mid
            c, d = c + lo_k * a, d + lo_k * b
        else:
            return m


# 1. médias
g_primeiro, g_ultimo = fr(txt[0]), fr(txt[-1])
media_verdadeira = (g_ultimo - g_primeiro) / (N - 1)
media_comprimento = Fraction(SUP - INF) / (N - 1)
loc = lambda t: 2 * math.pi / math.log(t / (2 * math.pi))
media_local_meio = loc(float((INF + SUP) / 2))
media_local_ini, media_local_fim = loc(float(INF)), loc(float(SUP))
medias = {
    "verdadeira (γ_último − γ_primeiro)/(N − 1)": {"fracao": reduz(media_verdadeira), "decimal": float(media_verdadeira),
                                                    "mdc_da_reducao": gcd(int((g_ultimo - g_primeiro) * 10 ** 17), (N - 1) * 10 ** 17)},
    "comprimento/(N − 1) = 3 360 000/14 380 682": {"fracao": reduz(media_comprimento), "decimal": float(media_comprimento),
                                                   "mdc_da_reducao": gcd(3360000, N - 1)},
    "local 2π/log(T/2π) no meio do bloco": media_local_meio,
    "local no início e no fim": [media_local_ini, media_local_fim],
    "diferença relativa verdadeira vs local": float(media_verdadeira) / media_local_meio - 1,
}

# 2. espaços extremos, exatos
ordem = np.argsort(g)
def espaco(j):
    c1, c2 = fr(txt[j]), fr(txt[j + 1])
    r1, r2 = fr(rad[j]), fr(rad[j + 1])
    gc = c2 - c1
    lo, hi = gc - (r1 + r2), gc + (r1 + r2)
    dif_txt = str(Decimal(txt[j + 1]) - Decimal(txt[j]))
    s_v = (lo / media_verdadeira, hi / media_verdadeira)
    s_c = (lo / media_comprimento, hi / media_comprimento)
    dl = loc(float(Decimal(txt[j])))
    simples = mais_simples(lo, hi)
    return {
        "zeros": [idx[j], idx[j + 1]],
        "centros": [txt[j], txt[j + 1]], "raios": [rad[j], rad[j + 1]],
        "gap_centros": {"decimal": dif_txt, "bruta": bruta(dif_txt), "reduzida": reduz(gc)},
        "gap_intervalo": [str(Decimal(lo.numerator) / Decimal(lo.denominator)), str(Decimal(hi.numerator) / Decimal(hi.denominator))],
        "largura_do_intervalo": float(hi - lo),
        "gap_fracao_mais_simples_na_bola": reduz(simples),
        "s_media_verdadeira": [float(s_v[0]), float(s_v[1])],
        "s_media_comprimento": [float(s_c[0]), float(s_c[1])],
        "s_media_local": [float(lo) / dl, float(hi) / dl],
        "um_sobre_s": [float(1 / s_v[1]), float(1 / s_v[0])],
        "lambda_colisao_intervalo": [float(-hi * hi / 2), float(-lo * lo / 2)],
        "lambda_errado_d2_8": float(-gc * gc / 8),
    }

curtos = [espaco(int(j)) for j in ordem[:8]]
longos = [espaco(int(j)) for j in ordem[::-1][:3]]

# 3. caudas nas duas normalizações (só contagens; a fronteira x é exata, o espaço vem do float com margem conferida)
s_v = g / float(media_verdadeira)
s_l = g / media_local_meio
caudas = {}
for nome, lim, lado in [("s < 1/400", 1 / 400, "<"), ("s < 1/300", 1 / 300, "<"), ("s < 1/100", 1 / 100, "<"),
                        ("s < 1/10", 1 / 10, "<"), ("s > 3", 3, ">"), ("s > 7/2", 3.5, ">"), ("s > 4", 4, ">")]:
    cv = int((s_v < lim).sum()) if lado == "<" else int((s_v > lim).sum())
    cl = int((s_l < lim).sum()) if lado == "<" else int((s_l > lim).sum())
    perto = int((np.abs(s_v - lim) < 1e-9).sum())
    q = Fraction(cv, N - 1)
    caudas[nome] = {"media_verdadeira": cv, "media_local": cl, "fracao": f"{q.numerator}/{q.denominator}",
                    "espacos_a_menos_de_1e-9_da_fronteira": perto}

# 4. absorção
soma_s_exata = (g_ultimo - g_primeiro) / media_verdadeira  # = N − 1 por telescopia
absorcao = {
    "soma_s_com_media_verdadeira": f"{soma_s_exata.numerator}/{soma_s_exata.denominator}",
    "N_menos_1": N - 1,
    "media_s_com_media_local": float(s_l.mean()),
    "s_min": float(s_v.min()), "s_max": float(s_v.max()),
    "Re_abs_faixa_para_b_3_5000": [0.5 + (float(s_v.min()) - 1) * 3 / 5000, 0.5 + (float(s_v.max()) - 1) * 3 / 5000],
}

# 5. toro
th = lambda s: 360 * (s - 1) / (s + 1)
toro = {"theta_s_min": th(float(s_v.min())), "theta_s_1_100": th(0.01), "theta_s_3": th(3.0),
        "theta_s_max": th(float(s_v.max())),
        "cauda_curta_s_menor_1_100_em_graus": [th(float(s_v.min())), th(0.01)],
        "cauda_longa_s_maior_3_em_graus": [th(3.0), th(float(s_v.max()))],
        "theta_de_71_10000": th(0.0071)}

out = {"N_zeros": N, "N_espacos": N - 1, "de": str(INF), "ate": str(SUP), "raio_max": str(rmax),
       "medias": medias, "espacos_mais_curtos": curtos, "espacos_mais_longos": longos, "caudas": caudas,
       "absorcao": absorcao, "toro": toro}
Path("gaps_em_fracoes.json").write_text(json.dumps(out, ensure_ascii=False, indent=1))
with open("gaps_em_fracoes.csv", "w", newline="") as f:
    w = csv.writer(f)
    w.writerow(["n", "n+1", "gap_centros_num", "gap_centros_den", "mdc_bruto", "gap_min_na_bola", "gap_max_na_bola",
                "gap_mais_simples_na_bola", "s_min", "s_max", "um_sobre_s_min", "um_sobre_s_max", "lambda_min",
                "lambda_max"])
    for e in curtos + longos:
        w.writerow([e["zeros"][0], e["zeros"][1], e["gap_centros"]["reduzida"]["num"],
                    e["gap_centros"]["reduzida"]["den"], e["gap_centros"]["bruta"]["mdc"], e["gap_intervalo"][0],
                    e["gap_intervalo"][1],
                    f'{e["gap_fracao_mais_simples_na_bola"]["num"]}/{e["gap_fracao_mais_simples_na_bola"]["den"]}',
                    f'{e["s_media_verdadeira"][0]:.12f}', f'{e["s_media_verdadeira"][1]:.12f}',
                    f'{e["um_sobre_s"][0]:.6f}', f'{e["um_sobre_s"][1]:.6f}',
                    f'{e["lambda_colisao_intervalo"][0]:.10e}', f'{e["lambda_colisao_intervalo"][1]:.10e}'])
print(json.dumps({"N": N, "raio_max": str(rmax), "medias": medias, "curto": curtos[0], "caudas": caudas,
                  "absorcao": absorcao, "toro": toro}, ensure_ascii=False, indent=1, default=str))
