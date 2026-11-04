"""Frações exatas do bloco contíguo e a "absorção do ½": o que é identidade, o que é aproximação, o que está errado.

    python3 absorcao.py DIR_C1 DIR_C2 > absorcao.json      (escreve também gaps_em_fracoes.csv)

DIR_C1 e DIR_C2 têm os zerosK.csv.gz das duas continuações (colunas indice, ordenada_meio, raio): 14 380 683 zeros
contíguos em (3 000 175 342 471,5; 3 000 178 702 471,5], todos na reta (README §31). Tudo é feito com inteiros na
escala 10⁻¹⁷ (os centros têm 17 casas) e com Fraction; nada de ponto flutuante nas contas que viram fração.

* gap exato g_n = γ_{n+1} − γ_n (diferença de centros) e o intervalo de verdade [g − r_n − r_{n+1}, g + r_n + r_{n+1}];
* média exata ḡ = (γ_último − γ_primeiro)/(n − 1) e a média "do bloco" 3 360 000/(n − 1), que não é a mesma coisa;
* s_n = g_n/ḡ: Σ s_n = n − 1 exatamente (telescópio), e por isso a média de ½ + b(s_n − 1) é ½ para todo b e todo
  bloco: identidade, não informação. Com a média do bloco a soma não fecha.
* contagens exatas das caudas (comparação de inteiros), o tempo de colisão −g²/2 do par mais apertado, e b(t).
"""
import csv
import glob
import gzip
import json
import sys
from fractions import Fraction
from math import gcd

ESC = 10 ** 17
A, B = Fraction(30001753424715, 10), Fraction(30001787024715, 10)


def centro_int(txt):
    inteiro, dec = txt.split(".")
    dec = (dec + "0" * 17)[:17]
    return int(inteiro) * ESC + int(dec)


def raio_int(txt):  # teto de raio·10¹⁷·10 (escala 10⁻¹⁸, para não perder o raio)
    return Fraction(txt) * ESC


def le(dirs):
    idx, cen, rai = [], [], []
    for d in dirs:
        fs = sorted(glob.glob(d + "/zeros*.csv.gz"), key=lambda p: int(p.split("zeros")[-1].split(".")[0]))
        for f in fs:
            with gzip.open(f, "rt") as h:
                next(h)
                for linha in h:
                    i, t, r = linha.rstrip("\n").split(",")
                    idx.append(int(i)); cen.append(centro_int(t)); rai.append(r)
    ordem = sorted(range(len(idx)), key=lambda k: idx[k])
    return [idx[k] for k in ordem], [cen[k] for k in ordem], [rai[k] for k in ordem]


def mais_simples(lo, hi):
    """A fração de menor denominador em [lo, hi] (Stern–Brocot), lo < hi positivos."""
    import math
    if math.floor(lo) < math.floor(hi) or lo == math.floor(lo):
        return Fraction(math.ceil(lo))
    n = math.floor(lo)
    r = mais_simples(1 / (hi - n), 1 / (lo - n))
    return n + 1 / r


def fr(x):
    x = Fraction(x)
    return f"{x.numerator}/{x.denominator}"


def main():
    idx, cen, rai = le(sys.argv[1:3])
    n = len(idx)
    assert all(b - a == 1 for a, b in zip(idx, idx[1:])), "índices não contíguos"
    assert Fraction(cen[0], ESC) > A and Fraction(cen[-1], ESC) <= B
    G = [b - a for a, b in zip(cen, cen[1:])]           # gaps em unidades de 10⁻¹⁷
    m = n - 1
    total = cen[-1] - cen[0]                             # Σ g_n (telescópio)
    assert sum(G) == total
    media = Fraction(total, ESC * m)
    media_bloco = Fraction(3360000, m)
    out = {"zeros": n, "gaps": m, "primeiro": [idx[0], fr(Fraction(cen[0], ESC))],
           "ultimo": [idx[-1], fr(Fraction(cen[-1], ESC))]}
    out["media_exata"] = {"fracao": fr(media), "decimal_20": f"{float(media):.15f}",
                          "mdc_prova": [gcd(total, ESC * m), "numerador e denominador divididos por este mdc"]}
    out["media_do_bloco"] = {"fracao": fr(media_bloco), "decimal": f"{float(media_bloco):.15f}",
                             "diferenca_para_a_exata": fr(media_bloco - media),
                             "por_que": "3 360 000 é o comprimento da janela, não γ_último − γ_primeiro"}
    # caudas exatas: s < p/q  ⟺  g·q·m·ESC < p·total·ESC/ESC  (tudo inteiro: g/ESC < (p/q)·total/(ESC·m))
    def conta(p, q, menor=True):
        if menor:
            return sum(1 for g in G if g * q * m < p * total)
        return sum(1 for g in G if g * q * m > p * total)
    caudas = {}
    for nome, p, q, menor in (("s<1/1000", 1, 1000, True), ("s<1/400", 1, 400, True), ("s<1/300", 1, 300, True),
                              ("s<1/100", 1, 100, True), ("s<1/10", 1, 10, True), ("s>2", 2, 1, False),
                              ("s>3", 3, 1, False), ("s>7/2", 7, 2, False), ("s>4", 4, 1, False)):
        c = conta(p, q, menor)
        caudas[nome] = {"pares": c, "fracao_dos_gaps": fr(Fraction(c, m))}
    out["caudas_com_media_exata"] = caudas
    # o par mais apertado
    k = min(range(m), key=lambda j: G[j])
    g = Fraction(G[k], ESC)
    rr = Fraction(rai[k]) + Fraction(rai[k + 1])
    s = g / media
    s_bloco = g / media_bloco
    lam = -g * g / 2
    out["par_mais_apertado"] = {
        "indices": [idx[k], idx[k + 1]], "centros": [fr(Fraction(cen[k], ESC)), fr(Fraction(cen[k + 1], ESC))],
        "gap_exato_dos_centros": fr(g), "gap_decimal": f"{float(g):.13e}",
        "raio_somado": str(float(rr)), "gap_na_bola": [fr(g - rr), fr(g + rr)],
        "gap_fracao_mais_simples_na_bola": fr(mais_simples(g - rr, g + rr)),
        "s_exato_media_exata": fr(s), "s_decimal": f"{float(s):.10f}",
        "s_com_media_do_bloco": fr(s_bloco),
        "s_menor_que_1_300": s < Fraction(1, 300), "s_menor_que_1_377": s < Fraction(1, 377),
        "lambda_colisao_menos_g2_sobre_2": fr(lam), "lambda_decimal": f"{float(lam):.6e}",
        "menos_g2_sobre_8": fr(-g * g / 8),
        "fator_4_e_coordenada": "−(2g)²/8 = −g²/2: em z = 2γ a distância é 2g; não há fator de vizinhos nesta conta",
    }
    # b(t) = √((t* − t)/2) do modelo isolado (Correcoes.bForcado), b² em fração exata
    bt = {}
    for t in (Fraction(-1, 10 ** 6), Fraction(-1, 10 ** 5), Fraction(-1, 10 ** 4), Fraction(-1, 10 ** 3)):
        b2 = (lam - t) / 2
        bt[fr(t)] = {"b_ao_quadrado": fr(b2), "b_decimal": f"{float(b2) ** 0.5:.6e}",
                     "Re_mais": f"{0.5 + float(b2) ** 0.5:.7f}", "Re_menos": f"{0.5 - float(b2) ** 0.5:.7f}"}
    out["b_do_par_no_fluxo"] = bt
    # absorção do ½
    soma_s = Fraction(total, ESC) / media                 # = m exatamente
    soma_s_bloco = Fraction(total, ESC) / media_bloco
    smin = Fraction(min(G), ESC) / media
    smax = Fraction(max(G), ESC) / media
    b = Fraction(3, 5000)
    out["absorcao"] = {
        "soma_s_media_exata": fr(soma_s), "igual_a_gaps": soma_s == m,
        "media_de_meio_mais_b_vezes_s_menos_1": fr(Fraction(1, 2) + b * (soma_s / m - 1)),
        "media_de_s_sobre_2": fr(soma_s / m / 2),
        "com_media_do_bloco": {"soma_s": fr(soma_s_bloco),
                               "media_de_s_sobre_2": fr(soma_s_bloco / m / 2),
                               "media_de_meio_mais_b_vezes_s_menos_1": fr(Fraction(1, 2) + b * (soma_s_bloco / m - 1))},
        "s_min": f"{float(smin):.6f}", "s_max": f"{float(smax):.6f}",
        "faixa_de_s_sobre_2": [f"{float(smin) / 2:.6f}", f"{float(smax) / 2:.6f}"],
        "faixa_de_meio_mais_b_vezes_s_menos_1_com_b_3_5000": [fr(Fraction(1, 2) + b * (smin - 1)),
                                                              fr(Fraction(1, 2) + b * (smax - 1))],
        "faixa_decimal": [f"{float(Fraction(1, 2) + b * (smin - 1)):.7f}", f"{float(Fraction(1, 2) + b * (smax - 1)):.7f}"],
    }
    # gaps_em_fracoes.csv: os 8 mais apertados e o maior vazio
    ordem = sorted(range(m), key=lambda j: G[j])[:8] + [max(range(m), key=lambda j: G[j])]
    with open("gaps_em_fracoes.csv", "w", newline="") as h:
        w = csv.writer(h)
        w.writerow(["lugar", "n", "gamma_n", "gamma_n1", "gap_exato_dos_centros", "gap_mais_simples_na_bola",
                    "s_exato", "s_decimal", "lambda_colisao_menos_gap2_sobre_2"])
        for c, j in enumerate(ordem):
            gj = Fraction(G[j], ESC)
            rj = Fraction(rai[j]) + Fraction(rai[j + 1])
            w.writerow(["maior vazio" if c == 8 else f"apertado {c + 1}", idx[j], fr(Fraction(cen[j], ESC)),
                        fr(Fraction(cen[j + 1], ESC)), fr(gj), fr(mais_simples(gj - rj, gj + rj)), fr(gj / media),
                        f"{float(gj / media):.10f}", fr(-gj * gj / 2)])
    print(json.dumps(out, ensure_ascii=False, indent=1))


main()
