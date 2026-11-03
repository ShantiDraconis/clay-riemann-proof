"""Modelo de matriz aleatória (Keating–Snaith): na altura T, ζ(½ + it) se comporta como o polinômio característico de
uma matriz unitária de Haar (CUE) de tamanho N = log(T/2π). Aqui: as lombadas desse polinômio.

    python3 cue.py N AMOSTRAS SAIDA.json [semente]

Para cada matriz: os autoângulos θ_j; Z_U(θ) = Π_j 2 sen((θ − θ_j)/2) é real e troca de sinal em cada θ_j (o análogo
de Z(t)); entre dois autoângulos consecutivos, o extremo θ* (onde Σ cot((θ* − θ_j)/2) = 0, por bissecção) e a
lombada h = |Z_U(θ*)|. Saem: a fração de lombadas abaixo de cada ε (o empurrão Z − ε da seção 28, com a
identificação |ζ| ↔ |Λ| de Keating–Snaith: E|ζ|² ≈ log(T/2π) ≈ N + 1 = E|Λ|²), média e variância de log h, quantis
baixos e o espaçamento normalizado mínimo. Modelo, não ζ.
"""
import json
import math
import sys
import time

import numpy as np

N, AM, SAI = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
rng = np.random.default_rng(int(sys.argv[4]) if len(sys.argv) > 4 else 1)
EPS = [1e-3, 3.2e-3, 1e-2, 0.1, 0.32, 1, 1.78, 3.16, 5.6, 10, 31.6, 129.5]


def haar(n):
    Z = (rng.standard_normal((n, n)) + 1j * rng.standard_normal((n, n))) / math.sqrt(2)
    Q, R = np.linalg.qr(Z)
    d = np.diag(R)
    return Q * (d / np.abs(d))


def lombadas(th):
    th = np.sort(np.mod(th, 2 * math.pi))
    a = th
    b = np.append(th[1:], th[0] + 2 * math.pi)
    lo, hi = a + 1e-13, b - 1e-13
    for _ in range(60):
        m = (lo + hi) / 2
        fp = (1 / np.tan((m[:, None] - th[None, :]) / 2)).sum(axis=1)
        pos = fp > 0
        lo = np.where(pos, m, lo)
        hi = np.where(pos, hi, m)
    m = (lo + hi) / 2
    logh = np.log(np.abs(2 * np.sin((m[:, None] - th[None, :]) / 2))).sum(axis=1)
    s = (b - a) * N / (2 * math.pi)
    return logh, s


t0 = time.time()
LH, S = [], []
for k in range(AM):
    th = np.angle(np.linalg.eigvals(haar(N)))
    lh, s = lombadas(th)
    LH.append(lh)
    S.append(s)
LH, S = np.concatenate(LH), np.concatenate(S)
h = np.exp(LH)
q = np.quantile(h, [1e-4, 1e-3, 1e-2, 0.1, 0.5]) if len(h) >= 10000 else np.quantile(h, [1e-3, 1e-2, 0.1, 0.5])
# cauda baixa: P(h < x) ≈ A·x^κ ajustado nos 2% menores (repulsão do GUE dá κ = 3/2)
hs = np.sort(h)
k2 = max(20, len(hs) // 50)
xs, ps = hs[:k2], (np.arange(1, k2 + 1)) / len(hs)
kappa, logA = np.polyfit(np.log(xs), np.log(ps), 1)
res = {"N": N, "amostras": AM, "lombadas": int(len(h)), "segundos": round(time.time() - t0, 1),
       "rms_teorico": math.sqrt(N + 1), "media_log_h": float(LH.mean()), "var_log_h": float(LH.var()),
       "mediana_h": float(np.median(h)), "quantis_h": [float(x) for x in q],
       "fracao_abaixo": {str(e): float((h < e).mean()) for e in EPS},
       "fracao_abaixo_relativo": {str(c): float((h < c * math.sqrt(N + 1)).mean()) for c in (0.01, 0.1, 0.3, 1, 3)},
       "cauda": {"kappa": float(kappa), "A": float(math.exp(logA))},
       "s_min": float(S.min()), "var_s": float(S.var()), "h_min": float(h.min())}
json.dump(res, open(SAI, "w"), indent=1)
print(json.dumps({k: v for k, v in res.items() if k not in ("fracao_abaixo",)}))
