"""O produto de Euler prevê as lombadas medidas? Teste nas 41 392 lombadas da faixa de 3·10¹² (seção 28).

Para cada lombada (extremo t* de Z entre dois zeros consecutivos, altura |Z*|, intervalo Δ): log|P_X(t*)| para
X = 10, 100, 1 000, 10 000. Mede a correlação de log|Z*| com log|P_X|, crua e depois de tirar a parte que vem do
intervalo (|Z*| ≈ |Z''|Δ²/8: regressão de log|Z*| em log Δ), e a lombada média nos 1% de t* com P_X menor e maior.
"""
import gzip
import json
import sys
from decimal import Decimal
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from euler import Fases  # noqa: E402

ARQ = Path(__file__).resolve().parents[1] / "forca" / "resultados" / "lombadas_faixa_3e12.json.gz"
d = json.load(gzip.open(ARQ))
L = d["lombadas"]
T0 = Decimal("3000175332800")
u = np.array([float(Decimal(l[4]) - T0) for l in L])
z = np.log(np.abs(np.array([l[2] for l in L])))
dl = np.log(np.array([l[1] for l in L]))
F = Fases(T0, 10000, 60)
res = {"lombadas": len(L), "X": {}}
A = np.vstack([dl, np.ones_like(dl)]).T
coef, *_ = np.linalg.lstsq(A, z, rcond=None)
resid = z - A @ coef
res["regressao_log_Zestrela_em_log_intervalo"] = {"inclinacao": coef[0], "r": float(np.corrcoef(dl, z)[0, 1])}
for X in (10, 100, 1000, 10000):
    lp = F.log_P(u, X).real
    r_cru = float(np.corrcoef(lp, z)[0, 1])
    r_res = float(np.corrcoef(lp, resid)[0, 1])
    o = np.argsort(lp)
    k = len(o) // 100
    res["X"][X] = {"desvio_log_P": float(lp.std()), "r_cru": r_cru, "r_sem_intervalo": r_res,
                   "mediana_Zestrela_1pc_menor_P": float(np.median(np.exp(z[o[:k]]))),
                   "mediana_Zestrela_1pc_maior_P": float(np.median(np.exp(z[o[-k:]]))),
                   "mediana_Zestrela_todas": float(np.median(np.exp(z))),
                   "fracao_menor_que_0_1_no_1pc_menor_P": float(np.mean(np.exp(z[o[:k]]) < 0.1)),
                   "fracao_menor_que_0_1_todas": float(np.mean(np.exp(z) < 0.1))}
    # o ponto mais fraco pelo produto: onde está a lombada mais baixa?
res["lombada_mais_baixa"] = {"indice": L[int(np.argmin(z))][0], "Zestrela": float(np.exp(z.min()))}
lp = F.log_P(u, 10000).real
res["posto_do_P_na_lombada_mais_baixa_pct"] = float((lp < lp[int(np.argmin(z))]).mean() * 100)
print(json.dumps(res, indent=1))
json.dump(res, open(Path(__file__).resolve().parent / "resultados" / "valida_3e12.json", "w"), indent=1)
