"""Cola as faixas de continua.py e procura os pares mais frágeis.

    python3 agrega.py faixas/ resultado/

1. Colagem: as faixas I e I+1 calculam N na mesma altura de forma independente (N(b_I) e N(a_{I+1})); tem que dar o
   mesmo inteiro. A parte contígua certificada vai de C0 até o fim da última faixa seguida sem falha.
2. Busca: o déficit (N(b) − N(a)) − (zeros na reta) de cada faixa. Déficit > 0 seria zero fora da reta.
3. Pares mais frágeis (fora do kernel, estimativa): espaçamento normalizado, Δ²g e λ de Csordas–Smith–Varga, com a
   mesma fórmula de computations/lehmer/analise.py (x = 2γ; g pela soma sobre a faixa mais a cauda pela densidade).
"""
import gzip
import json
import math
import sys
from decimal import Decimal
from pathlib import Path

import numpy as np

ENT, SAI = Path(sys.argv[1]), Path(sys.argv[2])
INICIO = json.loads((Path(__file__).parent / "inicio.json").read_text())
C0 = Decimal(INICIO["C0"])
SAI.mkdir(parents=True, exist_ok=True)
faixas = {}
for p in sorted(ENT.rglob("faixa*.json")):
    d = json.loads(p.read_text())
    faixas[int(d["faixa"])] = (d, p.parent)
out = {"faixas": {}, "colagem": [], "pares_mais_frageis": []}
contiguo_ok = True
# faixas extras (workflow_dispatch com faixas ≥ 4): a contiguidade conta a partir da primeira faixa presente; a colagem
# com as faixas de baixo (outra execução) é feita depois, juntando as pastas
I0 = min(faixas) if faixas else 0
contiguo_ate = C0 + I0 * Decimal(120000)
DE = contiguo_ate
if 0 in faixas:  # colagem com a execução anterior: N(C0) calculado de novo pela faixa 0
    out["colagem"].append({"altura": str(C0), "N_pela_faixa": faixas[0][0].get("N(a)"),
                           "N_pela_execucao_anterior": str(INICIO["N(C0)"]),
                           "confere": faixas[0][0].get("N(a)") == str(INICIO["N(C0)"])})
total_zeros = 0
todos_pares = []
for I in sorted(faixas):
    d, pasta = faixas[I]
    resumo = {k: v for k, v in d.items() if k not in ("blocos",)}
    out["faixas"][I] = resumo
    if I + 1 in faixas:
        prox = faixas[I + 1][0]
        out["colagem"].append({"altura": d["b"], "N_pela_faixa": d.get("N(b)"), "N_pela_seguinte": prox.get("N(a)"),
                               "confere": d.get("N(b)") is not None and d.get("N(b)") == prox.get("N(a)")})
    if contiguo_ok and d.get("certificado_ate") and Decimal(d["a"]) == contiguo_ate:
        contiguo_ate = Decimal(d["certificado_ate"])
        total_zeros += int(d["conferencia"]["zeros_na_reta"])
        if contiguo_ate != Decimal(d["b"]):
            contiguo_ok = False
    else:
        contiguo_ok = False
    # pares frágeis da faixa
    csv = pasta / f"zeros{I}.csv.gz"
    if not csv.exists():
        continue
    rows = [l.strip().split(",") for l in gzip.open(csv, "rt")][1:]
    if len(rows) < 5000:
        continue
    g0 = Decimal(rows[0][1])
    rel = np.array([float(Decimal(r[1]) - g0) for r in rows])
    G0 = float(g0)
    gaps = np.diff(rel)
    dens = math.log(G0 / (2 * math.pi)) / (2 * math.pi)
    s = gaps * dens
    x = 2 * rel
    n = len(x)
    rho_x = math.log(G0 / (2 * math.pi)) / (4 * math.pi)
    xL, xR = x[0], x[-1]
    MARG = 2000
    for k in sorted(np.argsort(gaps)[:200]):
        if k < MARG or k + 1 > n - 1 - MARG:
            continue
        xk, xk1 = x[k], x[k + 1]
        m = np.ones(n, bool)
        m[k] = m[k + 1] = False
        g = float(np.sum(1 / (xk - x[m]) ** 2) + np.sum(1 / (xk1 - x[m]) ** 2))
        g += sum(rho_x * (1 / (xx - xL) + 1 / (xR - xx)) for xx in (xk, xk1))
        D = xk1 - xk
        q = D * D * g
        lam = ((1 - 1.25 * q) ** 0.8 - 1) / (8 * g) if q < 0.8 else None
        todos_pares.append({"faixa": I, "k": rows[k][0], "gamma_k": rows[k][1], "gamma_k1": rows[k + 1][1],
                            "intervalo": float(gaps[k]), "espacamento_normalizado": float(s[k]),
                            "Delta2_g": float(q), "lehmer": bool(q < 0.8), "lambda_CSV": lam})
    out["faixas"][I]["estatistica"] = {"zeros": n, "s_min": float(s.min()), "s_medio": float(s.mean()),
                                       "variancia_s": float(s.var()), "variancia_GUE": 3 * math.pi / 8 - 1,
                                       "s_min_esperado_GUE": (9 / (math.pi ** 2 * n)) ** (1 / 3)}
todos_pares.sort(key=lambda r: -(r["lambda_CSV"] if r["lambda_CSV"] is not None else -1e9))
out["pares_mais_frageis"] = todos_pares[:20]
out["deficits"] = {I: faixas[I][0].get("conferencia", {}).get("deficit_(zeros_fora_da_reta)") for I in faixas}
out["falhas"] = {I: faixas[I][0].get("falhas") for I in faixas if faixas[I][0].get("falhas")}
out["colagem_ok"] = all(c["confere"] for c in out["colagem"])
out["contiguo"] = {"de": str(DE), "ate": str(contiguo_ate), "zeros_na_reta": total_zeros}
alguma_fora = any((v or 0) > 0 for v in out["deficits"].values())
paradas = {I: faixas[I][0]["parou_em"] for I in faixas if faixas[I][0].get("parou_em")}
if paradas:
    out["onde_examinar"] = {I: f"o método local não fechou perto do índice {n}: examinar essa altura com caixas e o "
                               f"princípio do argumento (pode ser dificuldade numérica ou zero fora da reta)"
                            for I, n in paradas.items()}
out["conclusao"] = (
    "ACHADO: déficit > 0 — zeros fora da reta indicados; isolar com caixas e o princípio do argumento"
    if alguma_fora else
    f"nenhum zero fora da reta em 0 < Re s < 1, {DE} < Im s ≤ {contiguo_ate} "
    f"({total_zeros} zeros, todos na reta)"
    + (f"; com as execuções anteriores, a seção 13 e Platt–Trudgian: RH conferida até {contiguo_ate}" if I0 == 0 else
       f"; falta colar com as faixas 0–{I0 - 1} (de {C0} a {DE}), calculadas em outra execução")
    if out["colagem_ok"] and contiguo_ate > DE else "inconclusivo: ver faixas")
(SAI / "continuacao.json").write_text(json.dumps(out, ensure_ascii=False, indent=1) + "\n")
print(json.dumps({k: v for k, v in out.items() if k not in ("faixas",)}, ensure_ascii=False, indent=1)[:6000])
