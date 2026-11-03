"""Força o quarteto no fluxo de de Bruijn: tempo de colisão de cada par frágil e o quarteto para t < t_c."""
import gzip, json, math, sys
from decimal import Decimal, getcontext
import numpy as np
getcontext().prec = 50
rows = [l.strip().split(",") for l in gzip.open(sys.argv[1], "rt")][1:]
idx = np.array([int(r[0]) for r in rows]); gd = [Decimal(r[1]) for r in rows]
g0 = gd[0]; rel = np.array([float(g - g0) for g in gd]); x = 2 * rel; n = len(x)
G0 = float(g0); rho_x = math.log(G0 / (2 * math.pi)) / (4 * math.pi)
gaps = np.diff(rel); ordem = np.argsort(gaps)[:5]
out = []
for k in ordem:
    m = np.ones(n, bool); m[k] = m[k + 1] = False
    def F(i):  # força dos outros zeros no fluxo dx/dt = 2 Σ 1/(x_i − x_j) (cauda pela densidade)
        f = 2 * np.sum(1 / (x[i] - x[m]))
        f += 2 * rho_x * (math.log(max(x[i] - x[0], 1e-9)) - math.log(max(x[-1] - x[i], 1e-9))) * 0  # cauda simétrica: ~0
        return f
    Frel = F(k + 1) - F(k)
    D = x[k + 1] - x[k]
    # u = Δ²: du/dt = 8 + 2√u·Frel (vizinhos congelados); t_c = −∫_0^{Δ²} du / (8 + 2√u Frel)
    us = np.linspace(0, D * D, 200001)
    integrando = 1 / (8 + 2 * np.sqrt(us) * Frel)
    tc = -np.trapezoid(integrando, us)
    centro = (gd[k] + gd[k + 1]) / 2
    quartetos = []
    for fator in (1.0001, 2.0, 10.0):
        t = fator * tc
        b = math.sqrt(2 * (tc - t)) / 2       # afastamento em Re s (lei da raiz quadrada, z = 2γ → s)
        quartetos.append({"t": t, "b": b, "zeros": [f"1/2 {sg1} {b:.3e} {sg2} i·{centro}" for sg1 in "+-" for sg2 in "+-"]})
    out.append({"k": int(idx[k]), "gamma_k": str(gd[k]), "gamma_k1": str(gd[k + 1]), "Delta_x": D,
                "t_colisao": tc, "par_isolado": -D * D / 8, "F_rel": Frel, "centro": str(centro), "quartetos": quartetos})
json.dump(out, open(sys.argv[2], "w"), ensure_ascii=False, indent=1)
for o in out:
    q = o["quartetos"][1]
    print(o["k"], o["centro"][:26], "t_c=%.6e" % o["t_colisao"], "(isolado %.6e)" % o["par_isolado"], "F_rel=%.3g" % o["F_rel"], "| t=2t_c: b=%.4e" % q["b"])
