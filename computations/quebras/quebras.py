"""Todas as quebras de tendência numa lista certificada de zeros de ζ (índice, ordenada, raio).

    python3 quebras.py ZEROS.csv.gz SAIDA.json [ROTULO]

A lista vem da Arb com o índice de cada zero certificado (contagem de Turing): N(t) = índice do último zero ≤ t.
Com θ(t) (série assintótica de Riemann–Siegel, 60 dígitos) e os pontos de Gram g_n (θ(g_n) = nπ, onde ζ(½ + ig_n) é
real), procura:

1. **Contagem**: N(t) − (zeros na reta até t) — zero se todos os zeros da lista estão na reta (é o que a Arb
   certifica); é a quebra que um zero fora da reta causaria.
2. **Lei de Gram**: S(g_n) = N(g_n) − n − 1 é inteiro; o ponto de Gram é "bom" se S(g_n) é par (ζ(½ + ig_n) > 0).
   Intervalos de Gram com 0 ou 2+ zeros.
3. **Regra de Rosser**: um bloco de Gram (entre dois pontos bons consecutivos, k intervalos) deve ter k zeros. As
   violações são a quebra clássica mais rara (a primeira está perto do zero 13 999 525, Lehman 1970).
4. **S(t)**: valor logo antes e logo depois de cada zero; extremos contra o teorema de Selberg (S tem média 0 e
   variância log log T / (2π²)).
5. **Espaçamentos extremos**: menor e maior espaçamento normalizado contra o GUE (Wigner): s_min ≈ (9/(π²N))^{1/3},
   s_max ≈ √((π/4) ln N).
6. **Pares de Lehmer com λ ≥ 0**: um par já colidido em t = 0 (λ de Csordas–Smith–Varga com os vizinhos da lista).

Cálculo fora do kernel. Nada aqui prova ou refuta RH.
"""
import bisect
import gzip
import json
import math
import sys
from decimal import Decimal, getcontext

getcontext().prec = 60
ENT, SAI = sys.argv[1], sys.argv[2]
ROTULO = sys.argv[3] if len(sys.argv) > 3 else ENT
PI = Decimal("3.14159265358979323846264338327950288419716939937510582097494459230781640628620899")

linhas = [l.strip().split(",") for l in gzip.open(ENT, "rt")][1:]
idx = [int(r[0]) for r in linhas]
gam = [Decimal(r[1]) for r in linhas]
rad = [Decimal(r[2]) for r in linhas]
n = len(gam)
assert all(idx[i + 1] == idx[i] + 1 for i in range(n - 1)), "índices não consecutivos"


def theta(t):
    """θ(t) = (t/2)log(t/2π) − t/2 − π/8 + 1/(48t) + 7/(5760t³) + 31/(80640t⁵) + … (t ≥ 10⁴: erro < 10⁻²⁰)."""
    return (t / 2) * (t / (2 * PI)).ln() - t / 2 - PI / 8 + 1 / (48 * t) + Decimal(7) / (5760 * t ** 3) \
        + Decimal(31) / (80640 * t ** 5)


def gram(m, t0):
    """g_m: θ(g_m) = mπ, por Newton a partir de t0 (θ'(t) = ½ log(t/2π))."""
    t = t0
    for _ in range(60):
        f = theta(t) - m * PI
        t2 = t - f / ((t / (2 * PI)).ln() / 2)
        if abs(t2 - t) < Decimal("1e-40"):
            return t2
        t = t2
    return t


# N(t) para t na faixa [γ_0, γ_{n−1}): índice do último zero ≤ t
def N(t):
    j = bisect.bisect_right(gam, t) - 1
    return idx[0] - 1 if j < 0 else idx[j]


m0 = int((theta(gam[0]) / PI).to_integral_value(rounding="ROUND_CEILING"))
m1 = int((theta(gam[-1]) / PI).to_integral_value(rounding="ROUND_FLOOR"))
gpts = []
t = gam[0]
for m in range(m0, m1 + 1):
    t = gram(m, t)
    gpts.append((m, t))
ambiguos = []
for m, g in gpts:
    j = bisect.bisect_left(gam, g)
    for jj in (j - 1, j):
        if 0 <= jj < n and abs(gam[jj] - g) <= rad[jj]:
            ambiguos.append({"m": m, "g": str(g)})
S_g = [(m, g, N(g) - m - 1) for m, g in gpts]
bons = [(m, g) for m, g, s in S_g if s % 2 == 0]
# lei de Gram: zeros em cada intervalo [g_m, g_{m+1})
cont = [N(gpts[i + 1][1]) - N(gpts[i][1]) for i in range(len(gpts) - 1)]
falhas_gram = sum(1 for c in cont if c != 1)
dist_cont = {str(k): cont.count(k) for k in sorted(set(cont))}
pontos_ruins = sum(1 for _, _, s in S_g if s % 2 != 0)
# blocos de Gram e regra de Rosser
blocos = []
for (ma, ga), (mb, gb) in zip(bons, bons[1:]):
    k = mb - ma
    z = N(gb) - N(ga)
    blocos.append((ma, mb, k, z, ga, gb))
rosser = [{"m_inicio": ma, "m_fim": mb, "comprimento": k, "zeros": z, "g_inicio": str(ga), "g_fim": str(gb)}
          for ma, mb, k, z, ga, gb in blocos if z != k]
dist_blocos = {}
for _, _, k, _, _, _ in blocos:
    dist_blocos[str(k)] = dist_blocos.get(str(k), 0) + 1
# S(t) nos zeros: logo depois S = idx − θ/π − 1, logo antes S − 1
S_dep = [float(idx[i] - theta(gam[i]) / PI - 1) for i in range(n)]
S_ant = [s - 1 for s in S_dep]
T = float(gam[n // 2])
var_selberg = math.log(math.log(T)) / (2 * math.pi ** 2)
smax_i = max(range(n), key=lambda i: S_dep[i])
smin_i = min(range(n), key=lambda i: S_ant[i])
# espaçamentos
rho = math.log(T / (2 * math.pi)) / (2 * math.pi)
rel = [float(g - gam[0]) for g in gam]
gaps = [rel[i + 1] - rel[i] for i in range(n - 1)]
s = [gp * rho for gp in gaps]
imin, imax = min(range(n - 1), key=lambda i: s[i]), max(range(n - 1), key=lambda i: s[i])
s_min_esp = (9 / (math.pi ** 2 * (n - 1))) ** (1 / 3)
s_max_esp = math.sqrt(math.pi / 4 * math.log(n - 1))
# λ de CSV nos 200 menores espaçamentos: algum ≥ 0?
x = [2 * r for r in rel]
rho_x = rho / 2
lam_max = None
for k in sorted(range(n - 1), key=lambda i: gaps[i])[:200]:
    if k < 300 or k + 1 > n - 301:
        continue
    g = sum(1 / (x[k] - x[j]) ** 2 + 1 / (x[k + 1] - x[j]) ** 2 for j in range(k - 300, k + 302) if j not in (k, k + 1))
    g += sum(rho_x * (1 / (xx - x[k - 300]) + 1 / (x[k + 301] - xx)) for xx in (x[k], x[k + 1]))
    D = x[k + 1] - x[k]
    q = D * D * g
    lam = ((1 - 1.25 * q) ** 0.8 - 1) / (8 * g) if q < 0.8 else None
    if lam is not None and (lam_max is None or lam > lam_max[0]):
        lam_max = (lam, idx[k], str(gam[k]))

out = {
    "rotulo": ROTULO, "zeros": n, "primeiro_indice": idx[0], "ultimo_indice": idx[-1],
    "faixa": [str(gam[0]), str(gam[-1])], "altura_media": T,
    "1_contagem": {"zeros_fora_da_reta_na_lista": 0,
                   "nota": "a Arb devolve cada zero com o índice fixado pela contagem de Turing: N(t) = zeros na reta"},
    "2_lei_de_gram": {"pontos_de_gram": len(gpts), "pontos_ruins": pontos_ruins,
                      "fracao_pontos_ruins": pontos_ruins / len(gpts), "intervalos_fora_da_lei": falhas_gram,
                      "fracao_intervalos_fora_da_lei": falhas_gram / max(len(cont), 1),
                      "zeros_por_intervalo": dist_cont, "pontos_ambiguos": ambiguos[:10]},
    "3_regra_de_rosser": {"blocos": len(blocos), "comprimento_dos_blocos": dist_blocos,
                          "violacoes": rosser, "n_violacoes": len(rosser)},
    "4_S_de_t": {"max_S": S_dep[smax_i], "em_zero": idx[smax_i], "gamma": str(gam[smax_i]),
                 "min_S": S_ant[smin_i], "em_zero_min": idx[smin_i], "gamma_min": str(gam[smin_i]),
                 "variancia_selberg": var_selberg, "desvio_selberg": math.sqrt(var_selberg),
                 "max_em_desvios": S_dep[smax_i] / math.sqrt(var_selberg),
                 "min_em_desvios": S_ant[smin_i] / math.sqrt(var_selberg)},
    "5_espacamentos": {"s_min": s[imin], "indice_s_min": idx[imin], "s_min_esperado_GUE": s_min_esp,
                       "s_max": s[imax], "indice_s_max": idx[imax], "gamma_s_max": str(gam[imax]),
                       "s_max_esperado_GUE": s_max_esp},
    "6_lehmer_com_lambda_nao_negativo": {"lambda_mais_perto_de_0": lam_max[0] if lam_max else None,
                                          "indice": lam_max[1] if lam_max else None,
                                          "pares_com_lambda_maior_ou_igual_a_0": 0 if (lam_max is None or lam_max[0] < 0) else 1},
}
json.dump(out, open(SAI, "w"), ensure_ascii=False, indent=1)
print(json.dumps({k: v for k, v in out.items() if k != "3_regra_de_rosser"}, ensure_ascii=False, indent=1))
print("Rosser:", len(rosser), "violações;", json.dumps(rosser[:10], ensure_ascii=False))
