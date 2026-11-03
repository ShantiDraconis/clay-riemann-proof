"""Janelas certificadas nas alturas onde um par de zeros fica mais frágil (FLINT 3 / Arb), em três etapas que
gravam cada número assim que ele existe.

    python3 alturas.py zeros    ./zeros SAIDA/ ORCAMENTO_s EXPOENTE N
    python3 alturas.py contagem ./zeros SAIDA/ ORCAMENTO_s EXPOENTE a|b PASTA_DOS_ZEROS
    python3 alturas.py fecha    SAIDA/ EXPOENTE PASTA [PASTA ...]

* `zeros`: os zeros de índice n₀−1 … n₀+N (n₀ ≈ N(10^e)) pelo método local de Platt, cada um como bola [t ± r] com
  Z(t) = 0, em blocos. Depois de CADA chamada da Arb grava `zeros_1eXX_bruto.csv.gz` (todos os zeros obtidos até ali)
  e `zeros_1eXX.json` (estado, blocos, falhas e, no fim, T_a e T_b: os pontos médios antes do primeiro e depois do
  último zero da janela). Não conta nada: um corte de tempo ou uma falha depois daqui não perde os zeros.
* `contagem`: N(T_a) (lado a) ou N(T_b) (lado b) pela contagem de Turing intervalar da Arb
  (`acb_dirichlet_zeta_nzeros`), lendo T_a, T_b do `zeros_1eXX.json`; grava `contagem_1eXX_a.json` ou `_b.json`. No
  workflow cada contagem é uma tarefa própria, em paralelo, com o seu orçamento (em 10¹⁸ uma contagem leva ≈ 6 000 s,
  e as duas depois dos zeros não cabiam no mesmo runner de 6 h: foi o que perdeu os 20 002 zeros de 10¹⁸ no run
  41588835957).
* `fecha`: junta zeros e contagens: confere o índice (N(T_a) = n₀ − 1), a contagem (N(T_b) − N(T_a) = N) e as bolas
  disjuntas, calcula os pares de Lehmer e a estatística dos espaçamentos e grava `alturas_1eXX.json` e, só se a janela
  fecha, `zeros_1eXX.csv.gz` (a lista certificada, que o ataque e os nós leem). Sem as duas contagens, a janela fica
  como "zeros achados, contagem pendente" e a lista bruta continua gravada.

O método local de Platt devolve menos zeros do que o pedido quando o pedido é grande (8 048 de 20 002 em 10¹⁴,
17 848 de 20 002 em 10¹⁸): cada chamada fica com os zeros que vieram (sem os MARGEM da ponta) e a próxima recomeça dali.

Pela lei da colisão (ClayRiemannProof/Colisao.lean), um par a distância Δ (em x = 2γ) sai da reta do fluxo de de
Bruijn em t = −Δ²/8; com os vizinhos, a cota de Csordas–Smith–Varga dá λ = ((1 − (5/4)Δ²g)^{4/5} − 1)/(8g). Com
Δ = 2·s/ρ (s o espaçamento normalizado, ρ = log(T/2π)/2π a densidade), o par mais frágil de uma janela de N zeros
na altura T tem λ ≈ −s_min²/(2ρ²), s_min ≈ (9/(π²N))^{1/3} (repulsão do GUE). Cálculo finito, fora do kernel.
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
PI = Decimal("3.14159265358979323846264338327950288419716939937510582097494459230781640628620899")
MARGEM, BLOCO = 40, 25000
INICIO = time.time()


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


def grava_json(arq, d):
    d["segundos_desta_etapa"] = round(time.time() - INICIO, 1)
    tmp = arq.with_suffix(".tmp")
    tmp.write_text(json.dumps(d, ensure_ascii=False, indent=1) + "\n")
    tmp.replace(arq)


def grava_lista(arq, n_primeiro, zs):
    tmp = arq.with_name(arq.name + ".tmp")
    with gzip.open(tmp, "wt") as f:
        f.write("indice,ordenada_meio,raio\n")
        for i, (m, rr) in enumerate(zs):
            f.write(f"{n_primeiro + i},{m},{rr}\n")
    tmp.replace(arq)


def le_lista(arq):
    with gzip.open(arq, "rt") as f:
        next(f)
        return [(int(a), Decimal(b), Decimal(c)) for a, b, c in (ln.strip().split(",") for ln in f if ln.strip())]


class Arb:
    def __init__(self, binario, orcamento):
        self.bin, self.orc = binario, orcamento

    def restante(self):
        return self.orc - (time.time() - INICIO)

    def roda(self, *args, timeout=None):
        timeout = max(60, min(timeout or self.restante(), self.restante()))
        t0 = time.time()
        r = subprocess.run([self.bin, *map(str, args)], capture_output=True, text=True, timeout=timeout)
        if r.returncode:
            raise RuntimeError(f"{args[:2]}: código {r.returncode}: {r.stderr[-300:]}")
        return json.loads(r.stdout), time.time() - t0


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


def etapa_zeros(binario, out, orcamento, e, N):
    arb = Arb(binario, orcamento)
    T = Decimal(10) ** e
    n0 = n_aprox(T)
    est = {"altura": f"1e{e}", "n0": str(n0), "N_pedido": N, "blocos": [], "falhas": [], "zeros_obtidos": 0}
    arq, lista = out / f"zeros_1e{e}.json", out / f"zeros_1e{e}_bruto.csv.gz"
    grava_json(arq, est)
    zs, n, seg_total = [], n0 - 1, 0.0  # zeros n0−1 … n0+N: um a mais de cada lado para os pontos médios
    try:
        while n <= n0 + N and arb.restante() > 300:
            k = min(BLOCO, n0 + N - n + 1)
            r, seg = arb.roda("platt", n - MARGEM, k + 2 * MARGEM, 320)
            todos = [bola(z) for z in r["zeros"]]
            fim = MARGEM + k if len(todos) >= k + 2 * MARGEM else len(todos) - MARGEM
            bl = todos[MARGEM:fim] if fim > MARGEM else []
            if len(bl) < k:
                est["falhas"].append({"n": str(n), "pedidos": k, "achados_brutos": len(todos), "aproveitados": len(bl)})
            if not bl:
                est["parou_em"] = str(n)
                break
            zs += bl
            seg_total += seg
            est["blocos"].append({"n": str(n), "achados": len(bl), "segundos": round(seg, 1)})
            n += len(bl)
            est["zeros_obtidos"] = len(zs)
            est["segundos_zeros"] = round(seg_total, 1)
            grava_lista(lista, n0 - 1, zs)  # cada bloco vai para o disco antes da próxima chamada
            grava_json(arq, est)
    except Exception as ex:  # noqa: BLE001
        est["erro"] = str(ex)[:500]
    if len(zs) >= 3:
        est["N"] = len(zs) - 2
        est["T_a"] = f"{(zs[0][0] + zs[1][0]) / 2:.12f}"
        est["T_b"] = f"{(zs[-2][0] + zs[-1][0]) / 2:.12f}"
        est["bolas_disjuntas"] = all(a[0] + a[1] < b[0] - b[1] for a, b in zip(zs, zs[1:]))
        est["maior_raio"] = str(max(rr for _, rr in zs))
    grava_json(arq, est)
    print(json.dumps(est, ensure_ascii=False)[:3000])


def etapa_contagem(binario, out, orcamento, e, lado, pasta):
    arb = Arb(binario, orcamento)
    arq = out / f"contagem_1e{e}_{lado}.json"
    res = {"altura": f"1e{e}", "lado": lado}
    try:
        z = json.loads((Path(pasta) / f"zeros_1e{e}.json").read_text())
        T = z["T_a" if lado == "a" else "T_b"]
        res["T"] = T
        grava_json(arq, res)
        r, seg = arb.roda("nzeros", T, 320, timeout=arb.restante() - 120)
        res.update({"N": str(inteiro(r["N"])), "segundos": round(seg, 1)})
    except Exception as ex:  # noqa: BLE001
        res["erro"] = str(ex)[:500]
    grava_json(arq, res)
    print(json.dumps(res, ensure_ascii=False))


def etapa_fecha(out, e, pastas):
    def acha(nome):
        for p in pastas:
            for q in Path(p).rglob(nome):
                return q
        return None

    j = {"altura": f"1e{e}"}
    zj = acha(f"zeros_1e{e}.json")
    if zj is None:
        j["erro"] = "etapa dos zeros sem resultado"
        grava_json(out / f"alturas_1e{e}_tentativa.json", {"janelas": [j]})
        return j
    z = json.loads(zj.read_text())
    j.update({k: z[k] for k in ("n0", "N_pedido", "falhas", "zeros_obtidos", "segundos_zeros", "N", "T_a", "T_b",
                                  "bolas_disjuntas", "maior_raio", "erro", "parou_em") if k in z})
    cont = {}
    for lado in "ab":
        c = acha(f"contagem_1e{e}_{lado}.json")
        if c is not None:
            cont[lado] = json.loads(c.read_text())
    lista = acha(f"zeros_1e{e}_bruto.csv.gz")
    if lista is not None and (out / lista.name).resolve() != lista.resolve():
        (out / lista.name).write_bytes(lista.read_bytes())
    ok = "N" in z and lista is not None and all("N" in cont.get(lado, {}) for lado in "ab")
    if not ok:
        j["conclusao"] = "zeros achados, contagem pendente" if "N" in z else "inconclusivo"
        j["contagens"] = cont
        # nome próprio: uma tentativa que não fecha não substitui o alturas_1eXX.json de uma janela certificada
        grava_json(out / f"alturas_1e{e}_tentativa.json", {"janelas": [j]})
        return j
    n0, N = int(z["n0"]), int(z["N"])
    Na, Nb = int(cont["a"]["N"]), int(cont["b"]["N"])
    zs = le_lista(lista)
    gam = [m for _, m, _ in zs[1:-1]]
    fecha = Na == n0 - 1 and Nb - Na == N and z["bolas_disjuntas"]
    j.update({"N(T_a)": str(Na), "N(T_b)": str(Nb),
              "segundos_contagem": round(cont["a"].get("segundos", 0) + cont["b"].get("segundos", 0), 1),
              "indice_confere": Na == n0 - 1, "contagem_fecha": Nb - Na == N,
              "primeiro": str(gam[0]), "ultimo": str(gam[-1]),
              "conclusao": ("nenhum zero fora da reta em 0 < Re s < 1, T_a < Im s ≤ T_b (contagem fecha)"
                            if fecha else "inconclusivo")})
    j["estatistica"] = lehmer(gam, Decimal(10) ** e)
    if fecha:
        grava_lista(out / f"zeros_1e{e}.csv.gz", n0, [(m, r) for _, m, r in zs[1:-1]])
    grava_json(out / (f"alturas_1e{e}.json" if fecha else f"alturas_1e{e}_tentativa.json"), {"fonte": "FLINT/Arb: acb_dirichlet_platt_local_hardy_z_zeros, "
                                             "acb_dirichlet_zeta_nzeros", "janelas": [j]})
    return j


if __name__ == "__main__":
    modo = sys.argv[1]
    if modo == "zeros":
        o = Path(sys.argv[3]); o.mkdir(parents=True, exist_ok=True)
        etapa_zeros(sys.argv[2], o, float(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]))
    elif modo == "contagem":
        o = Path(sys.argv[3]); o.mkdir(parents=True, exist_ok=True)
        etapa_contagem(sys.argv[2], o, float(sys.argv[4]), int(sys.argv[5]), sys.argv[6], sys.argv[7])
    elif modo == "fecha":
        o = Path(sys.argv[2]); o.mkdir(parents=True, exist_ok=True)
        r = etapa_fecha(o, int(sys.argv[3]), sys.argv[4:])
        print(json.dumps({k: v for k, v in r.items() if k not in ("estatistica", "falhas")}, ensure_ascii=False))
    else:
        raise SystemExit(__doc__)
