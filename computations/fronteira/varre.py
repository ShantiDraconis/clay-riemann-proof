"""Varredura de zeros de ζ numa altura grande atrás dos pares mais frágeis (FLINT 3 / Arb, método local de Platt).

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
    """Zeros n, n+1, … (até k). O método local de Platt devolve menos zeros que o pedido quando o pedido é grande
    (7 503 de 10 000 em 10¹³ no run 41557877448): fica com o que veio, sem os MARGEM da ponta (sem margem)."""
    tempo = max(60, min(3 * 3600, ORC - (time.time() - INICIO)))
    r = subprocess.run([BIN, "platt", str(n - MARGEM), str(k + 2 * MARGEM), "320"], capture_output=True, text=True,
                       timeout=tempo)
    if r.returncode:
        raise RuntimeError(r.stderr[-300:])
    todos = [bola(z) for z in json.loads(r.stdout)["zeros"]]
    fim = MARGEM + k if len(todos) >= k + 2 * MARGEM else len(todos) - MARGEM
    return todos[MARGEM:fim] if fim > MARGEM else []


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


n0 = n_aprox(Decimal(10) ** EXP) + DESL
rho = math.log(10.0 ** EXP / (2 * math.pi)) / (2 * math.pi)
rho_x = rho / 2
estado = {"expoente": EXP, "deslocamento": DESL, "n0": str(n0), "bloco": BLOCO, "zeros_varridos": 0,
          "pares_analisados": 0, "blocos": 0, "falhas": [], "densidade": rho, "maior_raio": "0",
          "hist_s": [0] * 40, "topo": []}
topo = []
n = n0
smin = 9.0
seguidas = 0
while time.time() - INICIO < ORC and seguidas < 5:
    t0 = time.time()
    try:
        zs = platt(n, BLOCO)
        if len(zs) < 2 * VIZ + 2:
            raise RuntimeError(f"{len(zs)} de {BLOCO} zeros")
    except Exception as ex:  # noqa: BLE001
        seguidas += 1
        if len(estado["falhas"]) < 50:
            estado["falhas"].append({"n": str(n), "erro": str(ex)[:200]})
        n += BLOCO - 2 * VIZ
        continue
    seguidas = 0
    L = len(zs)
    g0 = zs[0][0]
    x = [2 * float(m - g0) for m, _ in zs]
    estado["maior_raio"] = str(max(Decimal(estado["maior_raio"]), max(r for _, r in zs)))
    # pares do miolo [VIZ, L − VIZ − 1): cada par aparece no miolo de exatamente um bloco (o próximo bloco começa em
    # n + L − 2·VIZ − 1); o par k usa os zeros k − VIZ … k + 1 + VIZ, todos dentro do bloco
    for k in range(VIZ, L - VIZ - 1):
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
    estado["zeros_varridos"] += L - 2 * VIZ - 1
    estado["blocos"] += 1
    estado["ultimo_indice"] = str(n + L - VIZ - 1)
    estado["ultimo_gamma"] = str(zs[L - VIZ - 1][0])
    estado["s_min"] = smin
    estado["segundos_por_bloco"] = round(time.time() - t0, 1)
    estado["topo"] = topo
    estado["segundos"] = round(time.time() - INICIO, 1)
    json.dump(estado, open(SAIDA, "w"), ensure_ascii=False, indent=1)
    n += L - 2 * VIZ - 1
estado["topo"] = topo
estado["segundos"] = round(time.time() - INICIO, 1)
json.dump(estado, open(SAIDA, "w"), ensure_ascii=False, indent=1)
print(json.dumps({k: v for k, v in estado.items() if k not in ("topo", "hist_s")}, ensure_ascii=False))
