"""Janelas certificadas nas alturas onde um par de zeros fica mais frágil (FLINT 3 / Arb).

    python3 alturas.py ./zeros resultados/ [orcamento_s] [expoente N]

Com `expoente N`, só a altura 10^expoente (uma tarefa do workflow por altura, em paralelo); o resultado vai para
`alturas_1eXX.json` e `junta.py` monta o `alturas.json`. O método local de Platt devolve menos zeros do que o pedido
quando o pedido é grande (8 048 de 20 002 em 10¹⁴, 17 848 de 20 002 em 10¹⁸ no run 41554617926): cada chamada
fica com os zeros que vieram (sem os MARGEM da ponta, onde falta margem) e a próxima recomeça dali; o estado é gravado
depois de cada chamada e o orçamento é conferido entre elas, com uma reserva para as duas contagens de Turing. O custo
de uma chamada cresce com a altura e quase não depende do número de zeros pedidos (157 s em 10¹⁴, 336 s em 10¹⁶,
4 906 s em 10¹⁸); em 10²⁰ uma chamada não terminou em 4 h, e 10²⁰ e 10²² ficam fora do alcance deste método num
runner de 6 h.

Pela lei da colisão (ClayRiemannProof/Colisao.lean), um par a distância Δ (em x = 2γ) sai da reta do fluxo de de
Bruijn em t = −Δ²/8; com os vizinhos, a cota de Csordas–Smith–Varga dá λ = ((1 − (5/4)Δ²g)^{4/5} − 1)/(8g). Com
Δ = 2·s/ρ (s o espaçamento normalizado, ρ = log(T/2π)/2π a densidade), o par mais frágil de uma janela de N zeros
na altura T tem

    λ ≈ −s_min² / (2ρ²),   s_min ≈ (9/(π²N))^{1/3}  (repulsão do GUE),

que vai a 0⁻ quando T e N crescem: é nas alturas grandes que um quarteto apareceria primeiro, se aparecesse.

Para cada altura 10^e: os zeros de índice n₀ … n₀+N−1 (n₀ ≈ N(10^e)) pelo método local de Platt, cada um como bola
[t ± r] com Z(t) = 0; N(T) exato nos pontos médios antes do primeiro e depois do último (contagem de Turing) e a
conferência N(T_b) − N(T_a) = N; depois os pares de Lehmer da janela, a cota λ de cada um e a estatística dos
espaçamentos. Cálculo finito, fora do kernel.
"""
import gzip
import json
import math
import re
import subprocess
import sys
import time
from decimal import Decimal, getcontext
from pathlib import Path

getcontext().prec = 80
BIN = sys.argv[1]
OUT = Path(sys.argv[2])
OUT.mkdir(parents=True, exist_ok=True)
ORCAMENTO = float(sys.argv[3]) if len(sys.argv) > 3 else 5 * 3600
ALVOS = [(14, 20000), (16, 20000), (17, 20000), (18, 20000)]
if len(sys.argv) > 5:
    ALVOS = [(int(sys.argv[4]), int(sys.argv[5]))]
MARGEM, BLOCO = 40, 25000
ARQ = OUT / (f"alturas_1e{ALVOS[0][0]}.json" if len(sys.argv) > 5 else "alturas.json")
INICIO = time.time()
PI = Decimal("3.14159265358979323846264338327950288419716939937510582097494459230781640628620899")
estado = {"fonte": "FLINT/Arb: acb_dirichlet_platt_local_hardy_z_zeros, acb_dirichlet_zeta_nzeros", "janelas": []}


def grava():
    estado["segundos"] = round(time.time() - INICIO, 1)
    ARQ.write_text(json.dumps(estado, ensure_ascii=False, indent=1) + "\n")


def restante():
    return ORCAMENTO - (time.time() - INICIO)


def roda(*args, timeout=4 * 3600):
    timeout = max(60, min(timeout, restante()))
    t0 = time.time()
    r = subprocess.run([BIN, *map(str, args)], capture_output=True, text=True, timeout=timeout)
    if r.returncode:
        raise RuntimeError(f"{args[:2]}: código {r.returncode}: {r.stderr[-300:]}")
    return json.loads(r.stdout), time.time() - t0


def bola(s):
    m = re.match(r"\[?\s*([0-9.eE+-]+)\s*(?:\+/-\s*([0-9.eE+-]+))?\s*\]?", s)
    return Decimal(m.group(1)), Decimal(m.group(2) or "0")


def inteiro(s):
    meio, raio = bola(s)
    if raio != 0 or meio != meio.to_integral_value():
        raise ValueError(f"N(T) não é inteiro exato: {s}")
    return int(meio)


def n_aprox(T):
    x = T / (2 * PI)
    return int(x * (x.ln() - 1) + Decimal(7) / 8)


def lehmer(gam, T, k_max=120):
    """Pares de Lehmer entre os k_max menores intervalos: g pela janela + cauda pela densidade (estimativa)."""
    g0 = gam[0]
    rel = [float(g - g0) for g in gam]
    n = len(rel)
    x = [2 * r for r in rel]
    dens = math.log(float(T) / (2 * math.pi)) / (2 * math.pi)
    rho_x = dens / 2
    gaps = [rel[i + 1] - rel[i] for i in range(n - 1)]
    ordem = sorted(range(n - 1), key=lambda i: gaps[i])[:k_max]
    marg = max(50, n // 20)
    pares = []
    for k in ordem:
        if k < marg or k + 1 > n - 1 - marg:
            continue
        soma = 0.0
        for j in range(n):
            if j in (k, k + 1):
                continue
            soma += 1 / (x[k] - x[j]) ** 2 + 1 / (x[k + 1] - x[j]) ** 2
        cauda = sum(rho_x * (1 / (xx - x[0]) + 1 / (x[-1] - xx)) for xx in (x[k], x[k + 1]))
        g = soma + cauda
        D = x[k + 1] - x[k]
        q = D * D * g
        lam = ((1 - 1.25 * q) ** 0.8 - 1) / (8 * g) if q < 0.8 else None
        pares.append({"posicao": k, "gamma_k": str(gam[k]), "intervalo": gaps[k], "s": gaps[k] * dens,
                      "Delta2_g": q, "lehmer": q < 0.8, "lambda_CSV": lam, "par_isolado": -D * D / 8})
    pares.sort(key=lambda p: -(p["lambda_CSV"] if p["lambda_CSV"] is not None else -1e9))
    s = [gp * dens for gp in gaps]
    media = sum(s) / len(s)
    var = sum((v - media) ** 2 for v in s) / len(s)
    s_min = min(s)
    s_esp = (9 / (math.pi ** 2 * len(s))) ** (1 / 3)
    return {"densidade": dens, "s_medio": media, "variancia_s": var, "variancia_GUE_wigner": 3 * math.pi / 8 - 1,
            "s_min": s_min, "s_min_esperado_GUE": s_esp,
            "P(s<0.1)": sum(1 for v in s if v < 0.1) / len(s), "P(s<0.1)_GUE": math.pi ** 2 / 9 * 0.001,
            "lambda_previsto_com_s_min_observado": -s_min ** 2 / (2 * dens ** 2),
            "lambda_previsto_com_s_min_GUE": -s_esp ** 2 / (2 * dens ** 2),
            "n_lehmer": sum(p["lehmer"] for p in pares), "pares_mais_frageis": pares[:10]}


for e, N in ALVOS:
    if restante() < 600:
        estado["janelas"].append({"altura": f"1e{e}", "pulada": "orçamento de tempo"})
        grava()
        break
    T = Decimal(10) ** e
    n0 = n_aprox(T)
    reserva = 3600 if e >= 20 else 900  # tempo guardado para as duas contagens de Turing
    j = {"altura": f"1e{e}", "n0": str(n0), "N_pedido": N, "blocos": [], "falhas": []}
    estado["janelas"].append(j)
    grava()
    try:
        # zeros n0−1 … n0+N (um a mais de cada lado para os pontos médios), em blocos com margem
        zs, n, seg_total = [], n0 - 1, 0.0
        while n <= n0 + N and restante() > reserva:
            k = min(BLOCO, n0 + N - n + 1)
            r, seg = roda("platt", n - MARGEM, k + 2 * MARGEM, 320)
            todos = [bola(z) for z in r["zeros"]]
            # veio tudo: fica com o miolo; veio menos: fica com o que veio menos os MARGEM da ponta (sem margem)
            fim = MARGEM + k if len(todos) >= k + 2 * MARGEM else len(todos) - MARGEM
            bl = todos[MARGEM:fim] if fim > MARGEM else []
            if len(bl) < k:
                j["falhas"].append({"n": str(n), "pedidos": k, "achados_brutos": len(todos), "aproveitados": len(bl)})
            if not bl:
                j["parou_em"] = str(n)
                break
            zs += bl
            seg_total += seg
            j["blocos"].append({"n": str(n), "achados": len(bl), "segundos": round(seg, 1)})
            n += len(bl)
            j["zeros_obtidos"] = len(zs)
            grava()
        j["segundos_zeros"] = round(seg_total, 1)
        if len(zs) < 3:
            j["erro"] = f"só {len(zs)} zeros obtidos"
            grava()
            continue
        N = len(zs) - 2  # a janela certificada são os zeros n0 … n0+N−1 (o primeiro e o último dão os pontos médios)
        j["N"] = N
        disj = all(a[0] + a[1] < b[0] - b[1] for a, b in zip(zs, zs[1:]))
        Ta = (zs[0][0] + zs[1][0]) / 2
        Tb = (zs[-2][0] + zs[-1][0]) / 2
        r1, s1 = roda("nzeros", f"{Ta:.12f}", 320)
        r2, s2 = roda("nzeros", f"{Tb:.12f}", 320)
        Na, Nb = inteiro(r1["N"]), inteiro(r2["N"])
        gam = [m for m, _ in zs[1:-1]]
        j.update({
            "T_a": f"{Ta:.12f}", "T_b": f"{Tb:.12f}", "N(T_a)": str(Na), "N(T_b)": str(Nb),
            "segundos_contagem": round(s1 + s2, 1),
            "indice_confere": Na == n0 - 1,
            "contagem_fecha": Nb - Na == N,
            "bolas_disjuntas": disj, "maior_raio": str(max(rr for _, rr in zs)),
            "primeiro": str(gam[0]), "ultimo": str(gam[-1]),
            "conclusao": ("nenhum zero fora da reta em 0 < Re s < 1, T_a < Im s ≤ T_b (contagem fecha)"
                          if Na == n0 - 1 and Nb - Na == N and disj else "inconclusivo"),
        })
        j["estatistica"] = lehmer(gam, T)
        with gzip.open(OUT / f"zeros_1e{e}.csv.gz", "wt") as f:
            f.write("indice,ordenada_meio,raio\n")
            for i, (m, rr) in enumerate(zs[1:-1]):
                f.write(f"{n0 + i},{m},{rr}\n")
    except Exception as ex:  # noqa: BLE001
        j["erro"] = str(ex)[:500]
    grava()

print(json.dumps(estado, ensure_ascii=False, indent=1)[:6000])
