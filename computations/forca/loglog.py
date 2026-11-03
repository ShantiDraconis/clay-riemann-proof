"""Como a largura das lombadas cresce com a altura (lei log log T) e a extrapolação da fração tirada da reta.

    python3 loglog.py

Medido: as 41 392 lombadas da faixa de 3·10¹² (`resultados/lombadas_faixa_3e12.json.gz`) e uma amostra de 2 000
lombadas da janela certificada de 10¹⁴ (`resultados/lombadas_1e14_amostra.json.gz`, lombadas.py nos primeiros 2 001
zeros de `zeros_1e14.csv.gz`). Para cada uma: média e variância de log|Z*| (erro padrão por reamostragem) e a mesma
coisa normalizada pela média quadrática local de Conrey–Ghosh/Hughes–Lugmayer–Pearce-Crump
(√(aL + 2a + α₋₁), a = (e² − 5)/2, α₋₁ = 0,3689, L = log(T/2π)).

Modelo: o CUE de tamanho N = log(T/2π) (`computations/gigantes/resultados/cue_N*.json`, seção 35), calibrado nas
lombadas de 3·10¹². Ajuste var log h = A·log N + B nos sete tamanhos simulados (27 a 2 301); Selberg prevê A = ½
(Var log|ζ| ~ ½ log log T). Com a mediana constante (≈ 1,4) e essa variância, um modelo lognormal confere-se contra o
próprio CUE em N = 2 301 e depois extrapola para alturas que nenhuma simulação alcança: 10^(10^9), 10^(10^24) e a torre
10^(10^(11·10^7000000)), em logaritmos iterados. É extrapolação condicional (o CUE é modelo; a lei de Selberg é
teorema para t aleatório, não para lombadas).
"""
import gzip
import json
import math
from pathlib import Path
from statistics import NormalDist

import numpy as np

Phi = NormalDist().cdf
AQUI = Path(__file__).resolve().parent
G = AQUI.parent / "gigantes" / "resultados"
a = (math.e ** 2 - 5) / 2
am1 = 5 - math.e ** 2 - 10 * 0.5772156649015329 + 2 * math.e ** 2 * 0.5772156649015329
rng = np.random.default_rng(3)


def medida(arq, T):
    d = json.load(gzip.open(arq) if str(arq).endswith(".gz") else open(arq))
    z = np.abs(np.array([l[2] for l in d["lombadas"]], dtype=float))
    z = z[z > 0]
    lz = np.log(z)
    L = math.log(T / (2 * math.pi))
    rms = math.sqrt(a * L + 2 * a + am1)
    boot = [np.var(rng.choice(lz, len(lz))) for _ in range(400)]
    return {"lombadas": int(len(z)), "L": L, "media_log": float(lz.mean()), "var_log": float(lz.var()),
            "ep_var_log": float(np.std(boot)), "media_log_normalizada": float(lz.mean() - math.log(rms)),
            "mediana": float(np.median(z)), "fora_eps_1": float((z < 1).mean()),
            "fora_eps_rms_L": float((z < math.sqrt(L)).mean()), "rms_CG": rms,
            "media_Zestrela2": float((z ** 2).mean())}


res = {"medido": {}, "cue": {}, "ajuste": {}, "extrapolacao": {}}
res["medido"]["3e12"] = medida(AQUI / "resultados" / "lombadas_faixa_3e12.json.gz", 3000175332800.0)
f14 = AQUI / "resultados" / "lombadas_1e14_amostra.json.gz"
if f14.exists():
    res["medido"]["1e14"] = medida(f14, 1e14)

Ns, V, med = [], [], []
for f in sorted(G.glob("cue_N*.json"), key=lambda p: int(p.stem[5:])):
    c = json.loads(f.read_text())
    res["cue"][c["N"]] = {"var_log": c["var_log_h"], "mediana": c["mediana_h"], "lombadas": c["lombadas"],
                         "fora_eps_1": c["fracao_abaixo"]["1"], "fora_eps_rms": c["fracao_abaixo_relativo"]["1"]}
    Ns.append(c["N"]); V.append(c["var_log_h"]); med.append(c["mediana_h"])
Ns, V = np.array(Ns, float), np.array(V)
A, B = np.polyfit(np.log(Ns), V, 1)
mu = float(np.log(np.mean(med)))
res["ajuste"] = {"A": float(A), "B": float(B), "selberg_A": 0.5, "mediana_media": float(np.mean(med)),
                 "residuo_max": float(np.max(np.abs(V - (A * np.log(Ns) + B))))}


def lognormal(L, lnL=None):
    """Frações pelo modelo lognormal (mediana e^mu, variância A ln L + B). lnL em vez de L para L astronômico."""
    lnL = math.log(L) if lnL is None else lnL
    s2 = A * lnL + B
    s = math.sqrt(s2)
    out = {"var_log": s2, "fora_eps_1": Phi(-mu / s)}
    for c in (0.1, 0.3, 1):
        x = (math.log(c) + 0.5 * lnL - mu) / s  # ε = c·√L (√L ≈ média quadrática de Z)
        if x < 8:
            out[f"fora_eps_{c}_rms"] = Phi(x)
        else:  # 1 − Φ(x) ≈ φ(x)/x: em log10
            out[f"log10_fica_eps_{c}_rms"] = -(x * x / 2 + math.log(x * math.sqrt(2 * math.pi))) / math.log(10)
    return out


# conferência do esquema no próprio CUE (N = 2 301, o maior simulado)
res["ajuste"]["confere_N2301"] = {"lognormal": lognormal(2301), "cue": res["cue"].get(2301)}
res["ajuste"]["confere_N27"] = {"lognormal": lognormal(27), "cue": res["cue"].get(27),
                                "medido_3e12": {k: res["medido"]["3e12"][k] for k in ("fora_eps_1", "fora_eps_rms_L")}}
for nome, lnL in (("10^(10^9)", math.log(1e9 * math.log(10))), ("10^(10^24)", math.log(1e24 * math.log(10)))):
    res["extrapolacao"][nome] = lognormal(None, lnL)
# a torre 10^(10^(11·10^7000000)): ln L = 11·ln(10)·10^7000000 (+ ln ln 10), grande demais para ponto flutuante.
# var = A·ln L + B ≈ A·11·ln(10)·10^7000000; a fração que FICA na reta com ε = média quadrática é 1 − Φ(x) com
# x ≈ ½√(11·ln 10/A)·10^3500000, ou seja log10 ≈ −11·ln(10)/(8·A·ln 10)·10^7000000.
coef, e10 = 11 * math.log(10), 7_000_000
res["extrapolacao"]["10^(10^(11·10^7000000))"] = {
    "var_log": f"{A * coef:.3f}·10^{e10}",
    "dp": f"{math.sqrt(A * coef):.3f}·10^{e10 // 2}",
    "fora_eps_1": "→ 1/2 (Φ(−μ/σ) com σ astronômico)",
    "log10_fica_eps_rms": f"≈ −{coef / (8 * A * math.log(10)):.3f}·10^{e10}",
}
for nome, k in (("10^50", 50), ("10^100", 100), ("10^1000", 1000)):
    L = k * math.log(10) - math.log(2 * math.pi)
    res["extrapolacao"][nome] = lognormal(L)

(AQUI / "resultados" / "loglog.json").write_text(json.dumps(res, ensure_ascii=False, indent=1, default=str))
print(json.dumps(res, ensure_ascii=False, indent=1, default=str))
