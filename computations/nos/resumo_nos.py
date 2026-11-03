"""NOS.md: tabela dos nós atacados de todas as listas.

    python3 resumo_nos.py SAIDA.md ATACADOS.json…
"""
import json
import sys
from pathlib import Path

L = ["# Nós suspeitos e o ataque em cada um", "",
     "| lista | índices | t (início) | zeros | tipos | contagem local fecha | Platt de novo | Gram/Rosser/Turing |",
     "|---|---|---|---|---|---|---|---|"]
tot = fech = 0
for f in sys.argv[2:]:
    try:
        d = json.loads(Path(f).read_text())
    except Exception:  # noqa: BLE001
        continue
    for r in d["nos"]:
        if "pulado" in r:
            continue
        tot += 1
        fech += bool(r.get("contagem_fecha"))
        L.append(f"| {d.get('rotulo')} | {r['indice_inicio']}–{r['indice_fim']} | {r['t_inicio'][:24]} | {r['zeros_no_no']} | "
                 f"{'/'.join(r['tipos'])} | {r.get('contagem_fecha', r.get('erro', '—'))} | "
                 f"{r.get('platt_concorda_com_a_lista', '—')} | {r.get('hardy_concorda', r.get('hardy', '—'))} |")
L.insert(2, f"Nós atacados: {tot}; contagem local fechando (nenhum zero fora da reta no nó): {fech}.\n")
Path(sys.argv[1]).write_text("\n".join(L) + "\n")
print("\n".join(L[:40]))
