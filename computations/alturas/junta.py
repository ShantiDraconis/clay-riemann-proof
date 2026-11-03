"""Junta as janelas das tarefas por altura (alturas_1eXX.json) em alturas.json, na ordem das alturas.

    python3 junta.py PASTA_COM_AS_TAREFAS resultados/
"""
import json
import shutil
import sys
from pathlib import Path

ENT, SAI = Path(sys.argv[1]), Path(sys.argv[2])
SAI.mkdir(parents=True, exist_ok=True)
janelas, segundos, fonte = [], 0.0, None
for p in sorted(ENT.rglob("alturas_1e*.json"), key=lambda q: int(q.stem.split("1e")[1])):
    d = json.loads(p.read_text())
    fonte = d.get("fonte", fonte)
    segundos = max(segundos, d.get("segundos", 0))
    janelas += d.get("janelas", [])
    for z in p.parent.glob("zeros_1e*.csv.gz"):
        shutil.copy(z, SAI / z.name)
out = {"fonte": fonte, "janelas": janelas, "segundos": segundos}
(SAI / "alturas.json").write_text(json.dumps(out, ensure_ascii=False, indent=1) + "\n")
print(json.dumps([{k: v for k, v in j.items() if k not in ("estatistica", "blocos")} for j in janelas],
                 ensure_ascii=False, indent=1))
