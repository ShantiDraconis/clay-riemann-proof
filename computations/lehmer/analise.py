"""Pares de Lehmer, cota de Csordas–Smith–Varga e estatística de espaçamentos (GUE) nos 41 393 zeros certificados."""
import gzip, json, math, sys
from decimal import Decimal, getcontext
import numpy as np
getcontext().prec = 50
ent, sai = sys.argv[1], sys.argv[2]
rows = [l.strip().split(",") for l in gzip.open(ent, "rt")][1:]
idx = np.array([int(r[0]) for r in rows], dtype=np.int64)
g0 = Decimal(rows[0][1])
gam_d = [Decimal(r[1]) for r in rows]
rel = np.array([float(g - g0) for g in gam_d])          # γ − γ₀ (exato em double: < 1e4)
G0 = float(g0)
gaps = np.diff(rel)                                         # γ_{k+1} − γ_k
# densidade local e espaçamento normalizado (unfolding): N'(T) = log(T/2π)/(2π)
dens = math.log(G0 / (2 * math.pi)) / (2 * math.pi)
s = gaps * dens
# zeros de H₀: x = 2γ ; Δ = 2·gap ; g_k = Σ_{j≠k,k+1} 1/(x_k−x_j)² + 1/(x_{k+1}−x_j)²
x = 2 * rel
n = len(x)
rho_x = math.log(G0 / (2 * math.pi)) / (4 * math.pi)       # densidade em x
xL, xR = x[0], x[-1]
MARG = 2000
cand = np.argsort(gaps)[:400]                              # os 400 menores intervalos
res = []
for k in sorted(cand):
    if k < MARG or k + 1 > n - 1 - MARG:
        continue
    xk, xk1 = x[k], x[k + 1]
    m = np.ones(n, bool); m[k] = m[k + 1] = False
    soma = np.sum(1 / (xk - x[m]) ** 2) + np.sum(1 / (xk1 - x[m]) ** 2)
    # cauda (zeros fora da janela, e os negativos x_{−j} = −x_j): pela densidade, ρ·(1/(x−xL) + 1/(xR−x)) por ponto
    cauda = sum(rho_x * (1 / (xx - xL) + 1 / (xR - xx)) for xx in (xk, xk1))
    neg = 2 * rho_x / (2 * (G0 * 2))                       # Σ 1/(x+x_j)² ≈ ρ/(2x): desprezível
    g = soma + cauda + neg
    D = xk1 - xk
    q = D * D * g
    lam = ((1 - 1.25 * q) ** 0.8 - 1) / (8 * g) if q < 0.8 else None
    res.append({"k": int(idx[k]), "gamma_k": str(gam_d[k]), "gamma_k1": str(gam_d[k + 1]), "intervalo": float(gaps[k]),
                "espacamento_normalizado": float(s[k]), "Delta": float(D), "g": float(g), "Delta2_g": float(q),
                "lehmer": bool(q < 0.8), "lambda_CSV": lam, "colisao_par_isolado": -D * D / 8})
res.sort(key=lambda r: -(r["lambda_CSV"] if r["lambda_CSV"] is not None else -1e9))
# GUE: histograma do espaçamento normalizado contra a conjectura de Wigner para β = 2
hist, borda = np.histogram(s, bins=30, range=(0, 3), density=True)
meio = (borda[:-1] + borda[1:]) / 2
wigner = 32 / math.pi ** 2 * meio ** 2 * np.exp(-4 * meio ** 2 / math.pi)
poisson = np.exp(-meio)
# fração de espaçamentos pequenos: GUE prevê P(s < δ) ≈ (π²/9) δ³ para δ pequeno
peq = {str(d): {"observado": float(np.mean(s < d)), "GUE_pequeno_s": math.pi ** 2 / 9 * d ** 3} for d in (0.05, 0.1, 0.2)}
# correlação de pares (Montgomery): 1 − (sin πu / πu)²
uu = np.linspace(0.05, 3, 60)
cont = np.zeros_like(uu)
xs = rel * dens
for i in range(0, n, 7):
    d = xs[i + 1:i + 400] - xs[i]
    h, _ = np.histogram(d, bins=60, range=(0, 3.0))
    cont += h
cont = cont / (len(range(0, n, 7)) * (3.0 / 60))
mont = 1 - (np.sin(np.pi * uu) / (np.pi * uu)) ** 2
out = {"zeros": n, "densidade_por_unidade": dens, "espacamento_medio": 1 / dens,
       "s_min": float(s.min()), "s_max": float(s.max()), "s_medio": float(s.mean()),
       "variancia_s": float(s.var()), "variancia_GUE_wigner": (3 * math.pi / 8 - 1),
       "pares_lehmer_400_menores": res[:25], "n_lehmer": sum(r["lehmer"] for r in res),
       "pequenos": peq,
       "histograma": {"s": meio.tolist(), "observado": hist.tolist(), "wigner_GUE": wigner.tolist(), "poisson": poisson.tolist()},
       "correlacao_pares": {"u": uu.tolist(), "observado": cont.tolist(), "montgomery": mont.tolist()},
       "esperado_min_GUE": (9 / (math.pi ** 2 * n)) ** (1 / 3)}
json.dump(out, open(sai, "w"), ensure_ascii=False, indent=1)
print(json.dumps({k: v for k, v in out.items() if k not in ("histograma", "correlacao_pares", "pares_lehmer_400_menores")}, indent=1))
for r in res[:10]:
    print(r["k"], r["gamma_k"][:26], round(r["intervalo"], 6), round(r["espacamento_normalizado"], 5), "Δ²g=%.4g" % r["Delta2_g"], "λ=%.4g" % r["lambda_CSV"], "par isolado %.4g" % r["colisao_par_isolado"])
