"""Fecha cada altura (zeros + contagens de Turing) e junta tudo em alturas.json, sem perder o que já estava gravado.

    python3 junta.py PASTA_COM_AS_TAREFAS SAIDA/ [ALTURAS_EXISTENTE.json]

Para cada `zeros_1eXX.json` encontrado nas tarefas, `alturas.py fecha` confere índice, contagem e bolas e grava
`alturas_1eXX.json` (e `zeros_1eXX.csv.gz` se a janela fecha; a lista bruta `zeros_1eXX_bruto.csv.gz` sempre). Depois
junta com o `alturas.json` que já estava na branch de resultados: uma janela nova que fecha substitui a antiga da mesma
altura; uma que não fecha não apaga uma antiga certificada (vai para `tentativas`). As alturas que esta execução não
rodou ficam como estavam.
"""
import json
import shutil
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from alturas import etapa_fecha  # noqa: E402

ENT, SAI = Path(sys.argv[1]), Path(sys.argv[2])
SAI.mkdir(parents=True, exist_ok=True)
EXIST = Path(sys.argv[3]) if len(sys.argv) > 3 else None

expoentes = sorted({int(p.stem.split("1e")[1]) for p in ENT.rglob("zeros_1e*.json")})
novas = {}
for e in expoentes:
    novas[f"1e{e}"] = etapa_fecha(SAI, e, [ENT])
    for nome in (f"zeros_1e{e}.json", f"contagem_1e{e}_a.json", f"contagem_1e{e}_b.json"):
        for q in ENT.rglob(nome):
            shutil.copy(q, SAI / nome)
            break
for q in ENT.rglob("resultados-log-*.txt"):
    shutil.copy(q, SAI / q.name)

antigas, fonte = {}, "FLINT/Arb: acb_dirichlet_platt_local_hardy_z_zeros, acb_dirichlet_zeta_nzeros"
if EXIST and EXIST.exists() and EXIST.stat().st_size:
    d = json.loads(EXIST.read_text())
    fonte = d.get("fonte", fonte)
    for j in d.get("janelas", []):
        antigas[j["altura"]] = j


def fechou(j):
    return bool(j) and j.get("contagem_fecha") and j.get("indice_confere")


for alt, j in novas.items():
    velha = antigas.get(alt)
    if fechou(velha) and not fechou(j):
        velha.setdefault("tentativas", []).append({k: v for k, v in j.items() if k != "estatistica"})
    else:
        if velha and velha.get("tentativas"):
            j["tentativas"] = velha["tentativas"]
        antigas[alt] = j

janelas = [antigas[k] for k in sorted(antigas, key=lambda a: int(a.split("1e")[1]))]
(SAI / "alturas.json").write_text(json.dumps({"fonte": fonte, "janelas": janelas}, ensure_ascii=False, indent=1) + "\n")
print(json.dumps([{k: v for k, v in j.items() if k not in ("estatistica", "blocos", "falhas", "tentativas")}
                  for j in janelas], ensure_ascii=False, indent=1))
