"""Junta a validação, o CUE e as alturas gigantes numa tabela (resultados/RESUMO.md e resultados/resumo.json).

Para cada altura: N = log(T/2π) (tamanho do CUE de Keating–Snaith); do CUE, a mediana das lombadas, a fração de
pares tirados da reta pelos empurrões ε = 1 e ε = média quadrática (√(N+1)), e a lombada mínima esperada numa janela
de M zeros pela cauda P(h < x) ≈ A·x^κ (x_min = (1/(A·M))^{1/κ}); o λ do par mais apertado em M zeros pela
repulsão do GUE (λ ≈ −s_min²/(2ρ²), s_min = (9/(π²M))^{1/3}); e, das alturas gigantes, o vale mais fundo do produto
de Euler na janela varrida. Modelo (CUE, GUE) e medida (produto de Euler), marcados assim.
"""
import json
import math
from pathlib import Path

R = Path(__file__).resolve().parent / "resultados"
g = json.loads((R / "varredura_euler.json").read_text()) if (R / "varredura_euler.json").exists() else {}
alturas = [("3·10¹²", 12.477, 27), ("10¹⁴", 14, 30), ("10⁵⁰", 50, 113), ("10¹⁰⁰", 100, 228), ("10²⁵⁷", 257, 590),
           ("10⁵⁵⁷", 557, 1281), ("10¹⁰⁰⁰", 1000, 2301)]
linhas, out = [], {}
for nome, k, N in alturas:
    f = R / f"cue_N{N}.json"
    if not f.exists():
        continue
    c = json.loads(f.read_text())
    L = k * math.log(10) - math.log(2 * math.pi)
    rho = L / (2 * math.pi)
    A, kap = c["cauda"]["A"], c["cauda"]["kappa"]
    xmin = {M: (1 / (A * M)) ** (1 / kap) for M in (10 ** 4, 10 ** 6, 10 ** 9)}
    smin = (9 / (math.pi ** 2 * 1e4)) ** (1 / 3)
    lam = -smin ** 2 / (2 * rho ** 2)
    ge = g.get(f"1e{k}") if isinstance(k, int) else None
    v = ge["euler"]["vales"][0] if ge else None
    o = {"N": N, "mediana_lombada": c["mediana_h"], "var_log_lombada": c["var_log_h"],
         "fora_eps_1": c["fracao_abaixo"]["1"], "fora_eps_rms": c["fracao_abaixo_relativo"]["1"],
         "fora_eps_0_1_rms": c["fracao_abaixo_relativo"]["0.1"],
         "lombada_minima_em_M": xmin, "lambda_par_mais_apertado_1e4": lam, "espaco_medio": 1 / rho}
    if ge:
        o.update({"cota_N": ge["cota_HSW_de_N"], "digitos_N": ge["N_termo_principal_digitos"],
                  "termos_RS_log10": ge["custo"]["termos_RS_log10"], "Hiary_anos_log10":
                  ge["custo"]["anos_a_1e9_ops_por_s_Hiary_log10"], "vale": v, "desvio_log_P": ge["euler"]["desvio_log_P"]})
    out[nome] = o
    linhas.append(
        f"| {nome} | {N} | {c['mediana_h']:.2f} | {c['var_log_h']:.2f} | {100 * o['fora_eps_1']:.0f}% | "
        f"{100 * o['fora_eps_rms']:.1f}% | {xmin[10 ** 4]:.1e} | {xmin[10 ** 6]:.1e} | {lam:.1e} | "
        + (f"{v['t']} | {v['log_P']:.2f} ({v['desvios_abaixo_da_media']:.1f} σ) |" if v else "— | — |"))
cab = ("| altura | N do CUE | lombada mediana | var log lombada | fora com ε = 1 | fora com ε = √(N+1) | "
       "lombada mínima em 10⁴ zeros | em 10⁶ | λ do par mais apertado em 10⁴ zeros | vale mais fundo de P_X na janela | "
       "log\\|P_X\\| no vale |\n|---|---|---|---|---|---|---|---|---|---|---|")
(R / "RESUMO.md").write_text(cab + "\n" + "\n".join(linhas) + "\n")
(R / "resumo.json").write_text(json.dumps(out, ensure_ascii=False, indent=1))
print(cab)
print("\n".join(linhas))
