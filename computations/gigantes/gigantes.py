"""Como os zeros de ζ se comportariam em alturas gigantes: tudo o que depende só de L = ln T.

    python3 gigantes.py > gigantes.json

Nada aqui é cálculo de zeros: em T = 10^100000 a soma de Riemann–Siegel tem 10^50000 termos. O que se calcula são
as leis conhecidas, que dependem de T só por L = ln T:

* N(T) ≈ (T/2π)(ln(T/2π) − 1) + 7/8 (Riemann–von Mangoldt) e o espaçamento médio ⟨δ⟩ = 2π/ln(T/2π);
* |S(T)| ≤ min(0,1038 L + 0,2573 ln L + 8,3675; 0,1095 L + 0,2042 ln L + 3,0305), T ≥ e
  (Hasanalizade–Shen–Wong 2021), e o tamanho típico √(ln L/(2π²)) (Selberg);
* região sem zeros: β < 1 − w com w = máx(1/(5,558691 L), 1/(55,241 L^{2/3}(ln L)^{1/3}))
  (Mossinghoff–Trudgian–Yang 2022; |t| ≥ 3), logo um zero fora da reta teria b = |β − ½| < ½ − w;
* o par mais próximo esperado entre os N(T) zeros pelo GUE: s_min ≈ (9/(π² N))^{1/3}, Δγ = s_min·⟨δ⟩, e o tempo
  de colisão do modelo de de Bruijn λ ≈ −Δγ²/2 (coordenadas x = 2γ);
* o custo de um único valor de Z(t): √(T/2π) termos (Riemann–Siegel), T^{1/3} e T^{4/13} (Hiary).
"""
import json
import sys

sys.path.insert(0, "/home/claude/ext/mpmath")
from mpmath import mp, mpf, log, sqrt, pi, log10

mp.dps = 40
LN10 = log(10)
L2PI = log(2 * pi)

alturas = [
    ("3·10¹² (faixa contígua certificada)", log(mpf("3000175822471.5"))),
    ("10¹⁸ (Fronteira, 1ª onda)", 18 * LN10),
    ("10²³ (Odlyzko)", 23 * LN10),
    ("8,1·10³⁴ (Bober–Hiary, maior altura calculada)", log(mpf("8.1e34"))),
    ("10¹⁰⁰ (googol)", 100 * LN10),
    ("3^100000", 100000 * log(3)),
    ("10^100000", 100000 * LN10),
    ("2^1000000", 1000000 * log(2)),
    ("10^(10¹⁴)", mpf(10) ** 14 * LN10),
    ("10^(10¹⁰⁰) (googolplex)", mpf(10) ** 100 * LN10),
    ("10↑↑4 = 10^10^10^10", mp.exp(mpf(10) ** 10 * LN10) * LN10),
]


def fmt10(x):
    """x é log10 de um número; devolve 'a·10^b' (ou '10^(x)' se x for grande demais para escrever)."""
    if abs(x) > 10 ** 15:
        return f"10^({mp.nstr(x, 6)})"
    e = int(mp.floor(x))
    m = mpf(10) ** (x - e)
    return f"{mp.nstr(m, 4)}e{e}"


tabela = []
for nome, L in alturas:
    l = L - L2PI                      # ln(T/2π)
    lnL = log(L)
    log10N = l / LN10 + log10(l - 1)
    delta = 2 * pi / l
    Sbound = min(mpf("0.1038") * L + mpf("0.2573") * lnL + mpf("8.3675"),
                 mpf("0.1095") * L + mpf("0.2042") * lnL + mpf("3.0305"))
    Styp = sqrt(lnL / (2 * pi ** 2))
    w_cl = 1 / (mpf("5.558691") * L)
    w_kv = 1 / (mpf("55.241") * L ** (mpf(2) / 3) * lnL ** (mpf(1) / 3))
    w = max(w_cl, w_kv)
    log10_smin = (log10(mpf(9) / pi ** 2) - log10N) / 3
    log10_dg = log10_smin + log10(delta)
    log10_lam = 2 * log10_dg - log10(2)
    tabela.append({
        "altura": nome,
        "ln_T": mp.nstr(L, 8),
        "log10_N(T)": mp.nstr(log10N, 10),
        "espacamento_medio": mp.nstr(delta, 6),
        "S_cota_HSW": mp.nstr(Sbound, 6),
        "S_tipico_Selberg": mp.nstr(Styp, 4),
        "largura_sem_zeros_w": mp.nstr(w, 4),
        "regiao_usada": "Korobov–Vinogradov (MTY)" if w_kv > w_cl else "clássica (Mossinghoff–Trudgian)",
        "b_max_permitido": mp.nstr(mpf(1) / 2 - w, 10),
        "s_min_GUE": fmt10(log10_smin),
        "Delta_gamma_min": fmt10(log10_dg),
        "lambda_colisao_min": "−" + fmt10(log10_lam),
        "termos_Riemann_Siegel": fmt10(l / (2 * LN10)),
        "operacoes_Hiary_T^(1/3)": fmt10(L / (3 * LN10)),
        "operacoes_Hiary_T^(4/13)": fmt10(4 * L / (13 * LN10)),
    })
print(json.dumps(tabela, ensure_ascii=False, indent=1))
