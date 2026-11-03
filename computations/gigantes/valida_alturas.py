"""O produto de Euler nos pares das janelas certificadas de 10¹⁴, 10¹⁶ e 10¹⁷ (e na faixa de 3·10¹²).

Para cada intervalo entre zeros consecutivos: log|P_X| no ponto médio (X = 10 000) e o espaçamento normalizado s.
Mede a correlação de log s com log|P_X| e o posto (percentil) de P_X nos pares mais apertados de cada janela.
"""
import csv
import gzip
import json
import math
import sys
from decimal import Decimal
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from euler import Fases  # noqa: E402

PASTA = Path(sys.argv[1])  # pasta com zeros_1e14.csv.gz etc. (branch resultados-alturas)
res = {}
for e in (14, 16, 17):
    rows = list(csv.reader(gzip.open(PASTA / f"zeros_1e{e}.csv.gz", "rt")))[1:]
    g = [Decimal(r[1]) for r in rows]
    T0 = g[0].to_integral_value()
    rel = np.array([float(x - T0) for x in g])
    gap = np.diff(rel)
    mid = (rel[1:] + rel[:-1]) / 2
    dens = math.log(float(T0) / (2 * math.pi)) / (2 * math.pi)
    s = gap * dens
    F = Fases(T0, 10000, e + 40)
    lp = F.log_P(mid).real
    pct = lambda i: float((lp < lp[i]).mean() * 100)  # noqa: E731
    o = np.argsort(s)
    res[f"1e{e}"] = {"pares": len(s), "r_log_s_log_P": float(np.corrcoef(np.log(s), lp)[0, 1]),
                     "percentil_P_dos_10_mais_apertados": [round(pct(i), 1) for i in o[:10]],
                     "mediana_percentil_100_mais_apertados": float(np.median([pct(i) for i in o[:100]])),
                     "s_dos_10_mais_apertados": [round(float(s[i]), 4) for i in o[:10]]}
    print(e, json.dumps(res[f"1e{e}"]))
# a faixa de 3·10¹²: o percentil de P_X nos k menores |Z*|
d = json.load(gzip.open(Path(__file__).resolve().parents[1] / "forca" / "resultados" / "lombadas_faixa_3e12.json.gz"))
L = d["lombadas"]
T0 = Decimal("3000175332800")
u = np.array([float(Decimal(l[4]) - T0) for l in L])
z = np.abs(np.array([l[2] for l in L]))
lp = Fases(T0, 10000, 60).log_P(u).real
o = np.argsort(z)
rank = np.argsort(np.argsort(lp)) / len(lp) * 100
res["3e12_lombadas"] = {f"mediana_percentil_P_{k}_menores": float(np.median(rank[o[:k]])) for k in (10, 100, 1000)}
res["3e12_lombadas"]["percentil_P_10_menores"] = [round(float(rank[i]), 1) for i in o[:10]]
print(json.dumps(res["3e12_lombadas"]))
json.dump(res, open(Path(__file__).resolve().parent / "resultados" / "valida_alturas.json", "w"), indent=1)
