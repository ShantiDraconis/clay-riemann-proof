"""Junta as varreduras da fronteira: o par mais frágil de todas as alturas e o quarteto que o fluxo forçaria nele.

    python3 agrega.py PASTA_DAS_VARREDURAS SAIDA/
"""
import json
import math
import sys
from pathlib import Path

ent, sai = Path(sys.argv[1]), Path(sys.argv[2])
sai.mkdir(parents=True, exist_ok=True)
jobs = []
for f in sorted(ent.rglob("varre_*.json")):
    try:
        jobs.append(json.loads(f.read_text()))
    except Exception:  # noqa: BLE001
        pass
todos = []
resumo = []
for j in jobs:
    N = j.get("pares_analisados", 0)
    rho = j["densidade"]
    s_esp = (9 / (math.pi ** 2 * N)) ** (1 / 3) if N else None
    resumo.append({"expoente": j["expoente"], "deslocamento": j["deslocamento"], "n0": j["n0"],
                   "zeros_varridos": j.get("zeros_varridos", 0), "segundos": j.get("segundos"),
                   "segundos_por_bloco": j.get("segundos_por_bloco"), "falhas": len(j.get("falhas", [])),
                   "s_min": j.get("s_min"), "s_min_esperado_GUE": s_esp, "maior_raio": j.get("maior_raio"),
                   "lambda_previsto": (-(s_esp ** 2) / (2 * rho ** 2)) if s_esp else None,
                   "lambda_melhor": j["topo"][0]["lambda_CSV"] if j.get("topo") else None})
    for c in j.get("topo", []):
        c = dict(c)
        c["expoente"] = j["expoente"]
        todos.append(c)
todos.sort(key=lambda c: -c["lambda_CSV"])
for c in todos[:20]:
    tc = c["t_colisao"]
    b = math.sqrt(2 * abs(tc)) / 2
    gc = (float(c["gamma_k"]) + float(c["gamma_k1"])) / 2
    c["quarteto_em_2tc"] = {"t": 2 * tc, "b": b,
                            "zeros_de_H_t": f"1/2 ± {b:.4e} ± i·({c['gamma_k'][:30]} + {c['intervalo'] / 2:.6e})"}
total = sum(r["zeros_varridos"] for r in resumo)
out = {"zeros_varridos": total, "varreduras": resumo, "mais_frageis": todos[:20],
       "observacao": "zeros na reta (índice certificado pela Arb); λ e t_c com vizinhos ±300 e cauda pela densidade: "
                     "estimativa fora do kernel. Os quartetos são de H_t (t < 0), não de ζ."}
(sai / "fronteira.json").write_text(json.dumps(out, ensure_ascii=False, indent=1) + "\n")
linhas = [f"# Fronteira: os pares mais perto de sair da reta\n", f"Zeros varridos (todos na reta): {total}\n",
          "| altura | índice | γ_k | intervalo | s | λ (CSV) | t_c | b do quarteto em 2t_c |", "|---|---|---|---|---|---|---|---|"]
for c in todos[:20]:
    linhas.append(f"| 10^{c['expoente']} | {c['indice']} | {c['gamma_k'][:32]} | {c['intervalo']:.3e} | {c['s']:.5f} | "
                  f"{c['lambda_CSV']:.4e} | {c['t_colisao']:.4e} | {c['quarteto_em_2tc']['b']:.3e} |")
linhas += ["", "| altura | deslocamento | zeros | s_min | s_min GUE | λ melhor | λ previsto |", "|---|---|---|---|---|---|---|"]
for r in sorted(resumo, key=lambda r: (r["expoente"], r["deslocamento"])):
    f = lambda v, fmt: (fmt % v) if isinstance(v, (int, float)) else "—"
    linhas.append(f"| 10^{r['expoente']} | {r['deslocamento']} | {r['zeros_varridos']} | {f(r['s_min'], '%.5f')} | "
                  f"{f(r['s_min_esperado_GUE'], '%.5f')} | {f(r['lambda_melhor'], '%.3e')} | {f(r['lambda_previsto'], '%.3e')} |")
(sai / "RESUMO.md").write_text("\n".join(linhas) + "\n")
print("\n".join(linhas[:30]))
