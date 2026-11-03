"""As alturas 10^50, 10^100, 10^257, 10^557 e 10^1000: o que se calcula de verdade e o que o modelo diz.

    python3 varre_euler.py SAIDA.json [expoente ...]

Rigoroso (teoremas + aritmética exata em Decimal):
* N(T) pelo termo principal (T/2π)·log(T/2πe) + 7/8, com a cota explícita de Hasanalizade–Shen–Wong (2022,
  Corolário 1.2): |N(T) − (T/2π)log(T/2πe)| ≤ 0,1038 log T + 0,2573 log log T + 9,3675 para T ≥ e;
* o ponto de Gram mais próximo (θ(g_m) = mπ, série de Stirling de θ);
* o custo de calcular um único valor de Z(t): termos de Riemann–Siegel √(T/2π), operações T^{1/3} (Hiary, o melhor
  algoritmo implementado) e T^{4/13} (o melhor conhecido).
Medido nessas alturas (cálculo exato das fases t·log p mod 2π com expoente + 40 dígitos):
* o fator aritmético log|P_X(t)| (produto de Euler, X = 10⁵) na janela 10^k ≤ t ≤ 10^k + 200 (malha 0,004), e os vales mais fundos: os pontos onde a parte aritmética de ζ é mais fraca. Nas 41 392 lombadas medidas
  em 3·10¹², log|P_X| no extremo prevê log|Z*| com correlação 0,89 (valida.py): é onde as lombadas baixas (os pares
  mais fáceis de tirar da reta) se concentram. O que o produto não dá é a posição dos zeros nem a lombada exata.
"""
import json
import math
import sys
import time
from decimal import Decimal, getcontext
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent))
from euler import Fases, pi_decimal  # noqa: E402

SAI = Path(sys.argv[1])
KS = [int(x) for x in sys.argv[2:]] or [50, 100, 257, 557, 1000]
X, JANELA_U, PASSO = 100000, 200.0, 0.004  # P_X varia na escala 1/log X ≈ 0,09: a malha não precisa seguir os zeros
res = json.loads(SAI.read_text()) if SAI.exists() else {}
for k in KS:
    t0 = time.time()
    dig = k + 40
    getcontext().prec = dig + 10
    PI = pi_decimal(dig)
    getcontext().prec = dig + 10
    T = Decimal(10) ** k
    L = (T / (2 * PI)).ln()
    principal = T / (2 * PI) * (L - 1) + Decimal(7) / 8
    lnT = float(k * math.log(10))
    cota = 0.1038 * lnT + 0.2573 * math.log(lnT) + 9.3675
    theta = T / 2 * L - T / 2 - PI / 8 + 1 / (48 * T) + Decimal(7) / (5760 * T ** 3)
    m = int((theta / PI).to_integral_value(rounding="ROUND_FLOOR"))
    Lf = float(L)
    dens = Lf / (2 * math.pi)
    esp = 1 / dens
    F = Fases(T, X, dig)
    u = np.arange(0, JANELA_U, PASSO)
    lp = F.log_P(u).real
    # vales: mínimos locais, os 5 mais fundos (separados por pelo menos 3 espaçamentos)
    loc = np.nonzero((lp[1:-1] < lp[:-2]) & (lp[1:-1] < lp[2:]))[0] + 1
    loc = loc[np.argsort(lp[loc])]
    vales = []
    for i in loc:
        if all(abs(u[i] - v[0]) > 3 * esp for v in vales):
            vales.append((u[i], lp[i]))
        if len(vales) == 5:
            break
    mu, sd = float(lp.mean()), float(lp.std())
    giga = 1e9
    r = {
        "T": f"10^{k}", "log_T_sobre_2pi": Lf, "densidade": dens, "espaco_medio": esp,
        "N_termo_principal_digitos": len(str(int(principal))),
        "N_termo_principal_inicio": str(int(principal))[:40], "N_termo_principal_fim": str(int(principal))[-20:],
        "cota_HSW_de_N": cota,
        "gram_indice_m_inicio": str(m)[:40], "gram_indice_m_digitos": len(str(m)),
        "custo": {"termos_RS_log10": (k - math.log10(2 * math.pi)) / 2, "Hiary_t13_log10": k / 3,
                  "t413_log10": 4 * k / 13,
                  "anos_a_1e9_ops_por_s_Hiary_log10": k / 3 - math.log10(giga * 3.15e7)},
        "euler": {"X": X, "primos": int(len(F.p)), "janela_t": JANELA_U, "janela_espacos": JANELA_U * dens, "passo": PASSO, "pontos": int(len(u)),
                  "media_log_P": mu, "desvio_log_P": sd,
                  "vales": [{"t": f"10^{k} + {v[0]:.9f}", "u": float(v[0]), "log_P": float(v[1]),
                             "desvios_abaixo_da_media": (mu - float(v[1])) / sd} for v in vales],
                  "pico": {"u": float(u[int(np.argmax(lp))]), "log_P": float(lp.max())}},
        "segundos": round(time.time() - t0, 1)}
    res[f"1e{k}"] = r
    SAI.write_text(json.dumps(res, ensure_ascii=False, indent=1))
    print(k, json.dumps({kk: r[kk] for kk in ("densidade", "cota_HSW_de_N", "segundos")}),
          "vales:", [(round(v["u"], 6), round(v["log_P"], 2), round(v["desvios_abaixo_da_media"], 2))
                     for v in r["euler"]["vales"]], flush=True)
