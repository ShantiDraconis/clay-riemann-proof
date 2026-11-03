"""Varredura com detecção de quebras: pares frágeis e também lei de Gram, regra de Rosser e extremos de S(t).

Igual a computations/fronteira/varre.py; em cada bloco, com os índices certificados, calcula os pontos de Gram
(θ(g_m) = mπ), S(g_m) = N(g_m) − m − 1, os blocos de Gram e as violações da regra de Rosser, e S(t) logo antes e
logo depois de cada zero. Guarda as violações de Rosser e os maiores |S|.

Varredura de zeros de ζ numa altura grande atrás dos pares mais frágeis (FLINT 3 / Arb, método local de Platt).

    python3 varre.py ./zeros SAIDA.json EXPOENTE DESLOCAMENTO ORCAMENTO_S [BLOCO]

Começa no índice n₀ ≈ N(10^EXPOENTE) + DESLOCAMENTO e pede blocos de BLOCO zeros consecutivos até o orçamento de
tempo acabar. Cada zero sai da Arb como bola [t ± r] com Z(t) = 0 e índice certificado (contagem de Turing): todos os
zeros varridos estão em Re s = ½. Os blocos se sobrepõem em 2·VIZ zeros, de modo que todo par de vizinhos tem VIZ
zeros de cada lado dentro de algum bloco. Para cada par guarda:

* s = (γ_{k+1} − γ_k)·ρ, ρ = log(γ/2π)/2π  (espaçamento normalizado);
* Δ²g e λ de Csordas–Smith–Varga (x = 2γ; g com os VIZ vizinhos de cada lado e a cauda pela densidade);
* t_c, o tempo de colisão no fluxo de de Bruijn com os vizinhos congelados (README §16, §22).

O par com λ mais perto de 0⁻ é o mais perto de sair da reta: é ali que a deformação de de Bruijn cria o primeiro
quarteto. Cálculo fora do kernel; nada aqui prova ou refuta RH.
"""
import json
import math
import re
import subprocess
import sys
import time
from decimal import Decimal, getcontext

getcontext().prec = 80
BIN, SAIDA = sys.argv[1], sys.argv[2]
EXP, DESL, ORC = int(sys.argv[3]), int(sys.argv[4]), float(sys.argv[5])
BLOCO = int(sys.argv[6]) if len(sys.argv) > 6 else 10000
VIZ, MARGEM, TOPO = 300, 40, 40
PI = Decimal("3.14159265358979323846264338327950288419716939937510582097494459230781640628620899")
INICIO = time.time()


def n_aprox(T):
    x = T / (2 * PI)
    return int(x * (x.ln() - 1) + Decimal(7) / 8)


def bola(s):
    m = re.match(r"\[?\s*([0-9.eE+-]+)\s*(?:\+/-\s*([0-9.eE+-]+))?\s*\]?", s)
    return Decimal(m.group(1)), Decimal(m.group(2) or "0")


def platt(n, k):
    r = subprocess.run([BIN, "platt", str(n - MARGEM), str(k + 2 * MARGEM), "320"], capture_output=True, text=True,
                       timeout=3 * 3600)
    if r.returncode:
        raise RuntimeError(r.stderr[-300:])
    return [bola(z) for z in json.loads(r.stdout)["zeros"]][MARGEM:MARGEM + k]


def t_colisao(D, Frel):
    """t_c = −∫_0^{Δ²} du/(8 + 2√u·Frel)  (u = Δ², vizinhos congelados)."""
    m = 2000
    h = D * D / m
    tot = 0.0
    for i in range(m + 1):
        u = i * h
        w = 0.5 if i in (0, m) else 1.0
        tot += w / (8 + 2 * math.sqrt(u) * Frel)
    return -tot * h


def theta(t):
    return (t / 2) * (t / (2 * PI)).ln() - t / 2 - PI / 8 + 1 / (48 * t) + Decimal(7) / (5760 * t ** 3)


def gram(m, t0):
    t = t0
    for _ in range(60):
        t2 = t - (theta(t) - m * PI) / ((t / (2 * PI)).ln() / 2)
        if abs(t2 - t) < Decimal("1e-30"):
            return t2
        t = t2
    return t


def quebras_do_bloco(nini, zs, lo, hi):
    """Gram/Rosser/S nos zeros zs[lo:hi] (índices nini+lo …): violações de Rosser e extremos de S."""
    import bisect
    gs = [m for m, _ in zs]
    def N(t):
        j = bisect.bisect_right(gs, t) - 1
        return nini + j
    m0 = int((theta(gs[lo]) / PI).to_integral_value(rounding="ROUND_CEILING"))
    m1 = int((theta(gs[hi - 1]) / PI).to_integral_value(rounding="ROUND_FLOOR"))
    t = gs[lo]
    bons, ruins, fora_lei, prev = [], 0, 0, None
    for m in range(m0, m1 + 1):
        t = gram(m, t)
        Ng = N(t)
        if (Ng - m - 1) % 2 == 0:
            bons.append((m, t, Ng))
        else:
            ruins += 1
        if prev is not None and Ng - prev != 1:
            fora_lei += 1
        prev = Ng
    viol = []
    for (ma, ga, na), (mb, gb, nb) in zip(bons, bons[1:]):
        if nb - na != mb - ma:
            viol.append({"m": str(ma), "comprimento": mb - ma, "zeros": nb - na, "g": str(ga)[:30]})
    Sd = [(float(nini + i - theta(gs[i]) / PI - 1), nini + i) for i in range(lo, hi)]
    smax = max(Sd)
    smin = min((s - 1, i) for s, i in Sd)
    return {"gram": m1 - m0 + 1, "ruins": ruins, "fora_da_lei": fora_lei, "rosser": viol,
            "S_max": smax[0], "S_max_indice": str(smax[1]), "S_min": smin[0], "S_min_indice": str(smin[1])}


n0 = n_aprox(Decimal(10) ** EXP) + DESL
rho = math.log(10.0 ** EXP / (2 * math.pi)) / (2 * math.pi)
rho_x = rho / 2
estado = {"expoente": EXP, "deslocamento": DESL, "n0": str(n0), "bloco": BLOCO, "zeros_varridos": 0,
          "pares_analisados": 0, "blocos": 0, "falhas": [], "densidade": rho, "maior_raio": "0",
          "hist_s": [0] * 40, "topo": [], "gram": 0, "gram_ruins": 0, "gram_fora_da_lei": 0, "rosser": [],
          "S_max": None, "S_min": None}
topo = []
n = n0
smin = 9.0
seguidas = 0
while time.time() - INICIO < ORC and seguidas < 5:
    t0 = time.time()
    try:
        zs = platt(n, BLOCO)
        if len(zs) < BLOCO:
            raise RuntimeError(f"{len(zs)} de {BLOCO} zeros")
    except Exception as ex:  # noqa: BLE001
        seguidas += 1
        if len(estado["falhas"]) < 50:
            estado["falhas"].append({"n": str(n), "erro": str(ex)[:200]})
        n += BLOCO - 2 * VIZ
        continue
    seguidas = 0
    g0 = zs[0][0]
    x = [2 * float(m - g0) for m, _ in zs]
    estado["maior_raio"] = str(max(Decimal(estado["maior_raio"]), max(r for _, r in zs)))
    # pares do miolo [VIZ, BLOCO − VIZ): cada par aparece no miolo de exatamente um bloco
    for k in range(VIZ, BLOCO - VIZ):
        gap = (x[k + 1] - x[k]) / 2
        s = gap * rho
        estado["hist_s"][min(int(s / 0.1), 39)] += 1
        estado["pares_analisados"] += 1
        smin = min(smin, s)
        if s > 0.06 and len(topo) >= TOPO:
            continue
        D = x[k + 1] - x[k]
        lo, hi = k - VIZ, k + 1 + VIZ
        g = 0.0
        Fk = Fk1 = 0.0
        for j in range(lo, hi + 1):
            if j in (k, k + 1):
                continue
            g += 1 / (x[k] - x[j]) ** 2 + 1 / (x[k + 1] - x[j]) ** 2
            Fk += 2 / (x[k] - x[j])
            Fk1 += 2 / (x[k + 1] - x[j])
        g += sum(rho_x * (1 / (xx - x[lo]) + 1 / (x[hi] - xx)) for xx in (x[k], x[k + 1]))
        q = D * D * g
        lam = ((1 - 1.25 * q) ** 0.8 - 1) / (8 * g) if q < 0.8 else None
        if lam is None:
            continue
        cand = {"indice": str(n + k), "gamma_k": str(zs[k][0]), "gamma_k1": str(zs[k + 1][0]),
                "raio": str(max(zs[k][1], zs[k + 1][1])), "intervalo": gap, "s": s, "Delta2_g": q,
                "lambda_CSV": lam, "par_isolado": -D * D / 8, "t_colisao": t_colisao(D, Fk1 - Fk),
                "vizinhos": [round((x[j] - x[k]) / 2, 9) for j in range(k - 30, k + 32)]}
        topo.append(cand)
        topo.sort(key=lambda c: -c["lambda_CSV"])
        del topo[TOPO:]
    try:
        q = quebras_do_bloco(n, zs, VIZ, BLOCO - VIZ)
        estado["gram"] += q["gram"]
        estado["gram_ruins"] += q["ruins"]
        estado["gram_fora_da_lei"] += q["fora_da_lei"]
        if len(estado["rosser"]) < 200:
            estado["rosser"] += q["rosser"]
        if estado["S_max"] is None or q["S_max"] > estado["S_max"][0]:
            estado["S_max"] = [q["S_max"], q["S_max_indice"]]
        if estado["S_min"] is None or q["S_min"] < estado["S_min"][0]:
            estado["S_min"] = [q["S_min"], q["S_min_indice"]]
    except Exception as ex:  # noqa: BLE001
        estado["falhas"].append({"n": str(n), "erro_gram": str(ex)[:200]})
    estado["zeros_varridos"] += BLOCO - 2 * VIZ
    estado["blocos"] += 1
    estado["ultimo_indice"] = str(n + BLOCO - VIZ)
    estado["ultimo_gamma"] = str(zs[BLOCO - VIZ][0])
    estado["s_min"] = smin
    estado["segundos_por_bloco"] = round(time.time() - t0, 1)
    estado["topo"] = topo
    estado["segundos"] = round(time.time() - INICIO, 1)
    json.dump(estado, open(SAIDA, "w"), ensure_ascii=False, indent=1)
    n += BLOCO - 2 * VIZ
estado["topo"] = topo
estado["segundos"] = round(time.time() - INICIO, 1)
json.dump(estado, open(SAIDA, "w"), ensure_ascii=False, indent=1)
print(json.dumps({k: v for k, v in estado.items() if k not in ("topo", "hist_s")}, ensure_ascii=False))
