"""Quase-encontros de zeros em alturas gigantes: só leis e previsões (nenhum zero calculável lá).

    python3 quase_encontros_gigantes.py > quase_encontros_gigantes.json

Alturas: 10^10000, 10^111111, 10^1000000; "10^1000000^111111^10000" lido da esquerda, ((10^10⁶)^111111)^10000 =
10^(1,11111·10¹⁵); e lido como torre (convenção), 10^(10⁶^(111111^10000)) = 10^10^10^50458,3.
Para cada uma, com L = ln T: N(T) ≈ (T/2π)(ln(T/2π) − 1), ⟨δ⟩ = 2π/ln(T/2π), o par mais próximo esperado entre os
N(T) zeros (GUE, mediana) s_min = (9 ln 2/(π² N))^{1/3}, Δγ = s_min⟨δ⟩, λ ≈ −Δγ²/2; a largura da região sem
zeros w (Mossinghoff–Trudgian–Yang), o tamanho típico de S (Selberg) e o custo de um valor de Z(t) (√(T/2π) termos).
Valores grandes demais para escrever saem como log₁₀ (e log₁₀ log₁₀ na torre).
"""
import json
import sys

sys.path.insert(0, "/home/claude/ext/mpmath")
from mpmath import mp, mpf, log, log10, sqrt, pi

mp.dps = 60
LN10 = log(10)


def normal(nome, log10T):
    """log10T cabe num mpf: tudo por L = log10T·ln10."""
    L = log10T * LN10
    l = L - log(2 * pi)
    log10N = l / LN10 + log10(l - 1)
    delta = 2 * pi / l
    log10_smin = (log10(9 * log(2) / pi ** 2) - log10N) / 3
    log10_dg = log10_smin + log10(delta)
    log10_lam = 2 * log10_dg - log10(2)
    lnL = log(L)
    w = max(1 / (mpf("5.558691") * L), 1 / (mpf("55.241") * L ** (mpf(2) / 3) * lnL ** (mpf(1) / 3)))
    return {"altura": nome, "log10_T": mp.nstr(log10T, 12), "log10_N": mp.nstr(log10N, 12),
            "espacamento_medio": mp.nstr(delta, 6), "log10_s_min": mp.nstr(log10_smin, 10),
            "log10_Delta_gamma_min": mp.nstr(log10_dg, 10), "log10_abs_lambda_min": mp.nstr(log10_lam, 10),
            "pares_com_s_menor_1e-6": "10^" + mp.nstr(log10N + log10(pi ** 2 / 9) - 18, 10),
            "largura_sem_zeros_w": mp.nstr(w, 6), "S_tipico": mp.nstr(sqrt(lnL / (2 * pi ** 2)), 6),
            "cota_S_HSW": mp.nstr(mpf("0.1038") * L + mpf("0.2573") * lnL + mpf("8.3675"), 6),
            "log10_termos_Riemann_Siegel": mp.nstr(l / (2 * LN10), 10)}


saida = [normal("10^10000", mpf(10000)), normal("10^111111", mpf(111111)), normal("10^1000000", mpf(10) ** 6),
         normal("((10^1000000)^111111)^10000 = 10^(1,11111·10¹⁵)", mpf(1000000) * 111111 * 10000)]

# torre: T = 10^E, E = 10^(6·111111^10000); guardo ll = log10 log10 E = log10 6 + 10000·log10 111111
mp.dps = 80
ll = log10(6) + 10000 * log10(111111)          # log10 E = 10^ll
# log10 L = log10 E + log10 ln10 = 10^ll (a correção 0,36 some diante de 10^50458)
# ln L = 10^ll·ln10 + ln ln10  → S típico = √(ln L/(2π²)): log10 = (ll + log10(ln10/(2π²)))/2
log10_S_tip = (ll + log10(LN10 / (2 * pi ** 2))) / 2
saida.append({
    "altura": "10^1000000^111111^10000 como torre = 10^(10^(10^ll))", "ll": mp.nstr(ll, 12),
    "T": f"10^10^10^{mp.nstr(ll, 9)}",
    "N": f"≈ T (log10 N = log10 T + log10 L: 10^10^{mp.nstr(ll, 9)} + 10^{mp.nstr(ll, 9)})",
    "espacamento_medio": f"≈ 2π/L = 10^(−10^{mp.nstr(ll, 9)})",
    "s_min": f"10^(−(1/3)·10^10^{mp.nstr(ll, 9)})",
    "lambda_min": f"−10^(−(2/3)·10^10^{mp.nstr(ll, 9)})",
    "largura_sem_zeros_w": f"10^(−(2/3)·10^{mp.nstr(ll, 9)})",
    "S_tipico": f"10^{mp.nstr(log10_S_tip, 8)}",
    "cota_S_HSW": f"≈ 0,1038 L = 10^(10^{mp.nstr(ll, 9)} − 0,62)",
    "termos_Riemann_Siegel": f"10^((1/2)·10^10^{mp.nstr(ll, 9)})",
})
print(json.dumps(saida, ensure_ascii=False, indent=1))
