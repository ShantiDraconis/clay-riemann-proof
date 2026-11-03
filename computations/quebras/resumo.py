"""Tabela de todas as quebras de tendência: das listas completas (quebras.py) e das varreduras (varre2.py).

    python3 resumo.py SAIDA.md ARQUIVOS.json…
"""
import json
import math
import sys
from pathlib import Path

sai = Path(sys.argv[1])
L = ["# Quebras de tendência", "",
     "| conjunto | zeros | contagem (fora da reta) | Gram: pontos ruins | intervalos fora da lei | violações de Rosser | "
     "S máx (σ) | S mín (σ) | s_min / GUE | λ mais perto de 0 |", "|---|---|---|---|---|---|---|---|---|---|"]
eventos = []
for f in sys.argv[2:]:
    try:
        d = json.loads(Path(f).read_text())
    except Exception:  # noqa: BLE001
        continue
    if "2_lei_de_gram" in d:  # lista completa
        g, r, s, e, l6 = d["2_lei_de_gram"], d["3_regra_de_rosser"], d["4_S_de_t"], d["5_espacamentos"], d["6_lehmer_com_lambda_nao_negativo"]
        L.append(f"| {d['rotulo']} | {d['zeros']} | 0 | {g['fracao_pontos_ruins']:.1%} | {g['fracao_intervalos_fora_da_lei']:.1%} | "
                 f"{r['n_violacoes']} | {s['max_S']:.3f} ({s['max_em_desvios']:.1f}) | {s['min_S']:.3f} ({s['min_em_desvios']:.1f}) | "
                 f"{e['s_min']:.4f} / {e['s_min_esperado_GUE']:.4f} | {l6['lambda_mais_perto_de_0']:.3e} |")
        for v in r["violacoes"]:
            eventos.append((d["rotulo"], v["m_inicio"], v["comprimento"], v["zeros"], v["g_inicio"][:30]))
    elif "gram" in d:  # varredura
        T = 10.0 ** d["expoente"]
        sd = math.sqrt(math.log(math.log(T)) / (2 * math.pi ** 2))
        N = d.get("pares_analisados", 0) or 1
        smax = d.get("S_max") or [float("nan"), "—"]
        smin = d.get("S_min") or [float("nan"), "—"]
        lam = d["topo"][0]["lambda_CSV"] if d.get("topo") else float("nan")
        L.append(f"| varredura 10^{d['expoente']} +{d['deslocamento']} | {d['zeros_varridos']} | 0 | "
                 f"{d['gram_ruins'] / max(d['gram'], 1):.1%} | {d['gram_fora_da_lei'] / max(d['gram'], 1):.1%} | {len(d['rosser'])} | "
                 f"{smax[0]:.3f} ({smax[0] / sd:.1f}) | {smin[0]:.3f} ({smin[0] / sd:.1f}) | "
                 f"{d.get('s_min', float('nan')):.4f} / {(9 / (math.pi ** 2 * N)) ** (1 / 3):.4f} | {lam:.3e} |")
        for v in d["rosser"]:
            eventos.append((f"10^{d['expoente']}", v["m"], v["comprimento"], v["zeros"], v["g"]))
L += ["", "## Violações da regra de Rosser", "", "| conjunto | bloco começa no ponto de Gram m | comprimento | zeros | g_m |",
      "|---|---|---|---|---|"]
L += [f"| {a} | {b} | {c} | {d} | {e} |" for a, b, c, d, e in eventos]
sai.write_text("\n".join(L) + "\n")
print("\n".join(L))
