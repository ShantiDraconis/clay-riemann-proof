"""Ataque nos nós suspeitos: recalcula os zeros de cada nó com a Arb e faz a contagem de Turing local.

    python3 ataca_nos.py ./zeros NOS.json ZEROS.csv.gz SAIDA.json [MAX_NOS] [MAX_HARDY] [ORCAMENTO_S]

Para cada nó (índices a … b da lista certificada):

1. **De novo pelo método local de Platt**, com mais precisão (384 bits), os zeros a−1 … b+1: cada um tem de cair
   dentro da bola da lista (dois cálculos independentes concordando).
2. **Pelo método geral** (Gram/Rosser/Turing da Arb, `acb_dirichlet_hardy_z_zeros`) nos MAX_HARDY nós mais fortes:
   outro algoritmo, mesmos zeros.
3. **Contagem de Turing local**: N(T) exato em T_a = (γ_{a−1} + γ_a)/2 e T_b = (γ_b + γ_{b+1})/2. Se
   N(T_a) = a − 1 e N(T_b) = b, os b − a + 1 zeros do nó, todos em Re s = ½, são os únicos zeros de ζ com
   0 < Re s < 1 e T_a < Im s ≤ T_b: nenhum zero fora da reta, nenhum quarteto, no nó.

Cálculo fora do kernel. Nada aqui prova ou refuta RH.
"""
import gzip
import json
import re
import subprocess
import sys
import time
from decimal import Decimal, getcontext

getcontext().prec = 80
BIN, NOS, LISTA, SAI = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
MAXN = int(sys.argv[5]) if len(sys.argv) > 5 else 25
MAXH = int(sys.argv[6]) if len(sys.argv) > 6 else 6
ORC = float(sys.argv[7]) if len(sys.argv) > 7 else 4 * 3600
INICIO = time.time()


def bola(s):
    m = re.match(r"\[?\s*([0-9.eE+-]+)\s*(?:\+/-\s*([0-9.eE+-]+))?\s*\]?", s)
    return Decimal(m.group(1)), Decimal(m.group(2) or "0")


def roda(*args, timeout=3600):
    r = subprocess.run([BIN, *map(str, args)], capture_output=True, text=True, timeout=timeout)
    if r.returncode:
        raise RuntimeError(r.stderr[-300:])
    return json.loads(r.stdout)


lista = {}
for l in gzip.open(LISTA, "rt"):
    p = l.strip().split(",")
    if p[0].isdigit():
        lista[int(p[0])] = (Decimal(p[1]), Decimal(p[2]))
nos = json.load(open(NOS))
res = {"rotulo": nos.get("rotulo"), "nos": []}
for k, no in enumerate(nos["nos"][:MAXN]):
    if time.time() - INICIO > ORC:
        res["nos"].append({"indice_inicio": no["indice_inicio"], "pulado": "orçamento"})
        continue
    a, b = int(no["indice_inicio"]), int(no["indice_fim"])
    r = {"indice_inicio": a, "indice_fim": b, "zeros_no_no": b - a + 1, "tipos": no["tipos"], "pontos": no["pontos"],
         "t_inicio": no["t_inicio"], "t_fim": no["t_fim"], "detalhes": no["detalhes"][:4]}
    try:
        M = 40
        t0 = time.time()
        zs = [bola(x) for x in roda("platt", a - 1 - M, b - a + 3 + 2 * M, 384)["zeros"]][M:M + b - a + 3]
        r["segundos_platt"] = round(time.time() - t0, 1)
        dif = []
        for j, (m, rr) in enumerate(zs):
            i = a - 1 + j
            if i in lista:
                g, rl = lista[i]
                dif.append(abs(m - g) <= rl + rr + Decimal("1e-25"))
        r["platt_concorda_com_a_lista"] = all(dif) and len(dif) > 0
        r["maior_raio"] = str(max(rr for _, rr in zs))
        Ta = (zs[0][0] + zs[1][0]) / 2
        Tb = (zs[-2][0] + zs[-1][0]) / 2
        Na = int(bola(roda("nzeros", f"{Ta:.15f}", 384)["N"])[0])
        Nb = int(bola(roda("nzeros", f"{Tb:.15f}", 384)["N"])[0])
        r.update({"T_a": f"{Ta:.15f}", "T_b": f"{Tb:.15f}", "N(T_a)": Na, "N(T_b)": Nb,
                  "contagem_fecha": Na == a - 1 and Nb == b})
        if k < MAXH:
            t0 = time.time()
            try:
                hz = [bola(x) for x in roda("hardy", a, b - a + 1, 256, timeout=1500)["zeros"]]
                r["hardy_concorda"] = all(abs(hz[j][0] - zs[j + 1][0]) <= hz[j][1] + zs[j + 1][1] + Decimal("1e-25")
                                          for j in range(len(hz)))
                r["segundos_hardy"] = round(time.time() - t0, 1)
            except Exception as ex:  # noqa: BLE001
                r["hardy"] = f"não feito: {str(ex)[:120]}"
        r["veredito"] = ("os zeros do nó estão todos na reta e são os únicos de ζ em 0 < Re s < 1 nessa faixa de alturas"
                         if r.get("contagem_fecha") and r.get("platt_concorda_com_a_lista") else "ver números")
    except Exception as ex:  # noqa: BLE001
        r["erro"] = str(ex)[:300]
    res["nos"].append(r)
    json.dump(res, open(SAI, "w"), ensure_ascii=False, indent=1)
json.dump(res, open(SAI, "w"), ensure_ascii=False, indent=1)
print(json.dumps([{k: v for k, v in r.items() if k in ("indice_inicio", "tipos", "contagem_fecha", "platt_concorda_com_a_lista",
                                                        "hardy_concorda", "veredito", "erro")} for r in res["nos"]],
                 ensure_ascii=False, indent=0)[:4000])
