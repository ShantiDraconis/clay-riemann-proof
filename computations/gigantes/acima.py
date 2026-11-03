"""Só as escalas acima do que já foi verificado: o que se espera de zeros e de pares quase colidindo em alturas que
ninguém calculou (10¹⁹ até 10↑↑4). Nada aqui é cálculo de zero; é previsão (GUE) e cota provada.

    python3 acima.py   (grava acima.json e acima.png)

Para cada altura T, com ⟨δ⟩ = 2π/ln(T/2π) e densidade ρ = ln(T/2π)/(2π) zeros por unidade de altura:
* par mais frágil esperado entre os N(T) zeros: s_min ≈ (9/(π² N))^{1/3}, Δγ = s_min ⟨δ⟩, λ ≈ −Δγ²/2;
* pares mais frágeis que o recorde já visto (|λ| < 4,59·10⁻⁷, o par 12 363 153 756 750/751): a fração de
  espaçamentos com s < s* = √(2·4,59·10⁻⁷)/⟨δ⟩ pela distribuição de Wigner do GUE,
  P(s < x) = erf(2x/√π) − (4x/π) e^{−4x²/π} (≈ 1,08 x³ para x pequeno), e a altura média entre dois deles
  é 1/(ρ P);
* faixa onde um zero fora da reta ainda é permitido: b < ½ − w, w da região sem zeros (Mossinghoff–Trudgian–Yang).
"""
import json
import sys

sys.path.insert(0, "/home/claude/ext/mpmath")
from mpmath import mp, mpf, log, sqrt, pi, log10, erf, exp

mp.dps = 40
LN10 = log(10)
L2PI = log(2 * pi)
RECORDE = mpf("4.593e-7")
alturas = [
    ("10¹⁹", 19 * LN10), ("10²⁰", 20 * LN10), ("10²²", 22 * LN10), ("10²⁴", 24 * LN10), ("10³⁰", 30 * LN10),
    ("10⁴⁰", 40 * LN10), ("10¹⁰⁰", 100 * LN10), ("3^100000", 100000 * log(3)), ("10^100000", 100000 * LN10),
    ("2^1000000", 1000000 * log(2)), ("10^(10¹⁴)", mpf(10) ** 14 * LN10), ("googolplex", mpf(10) ** 100 * LN10),
    ("10↑↑4", mp.exp(mpf(10) ** 10 * LN10) * LN10),
]
out = []
for nome, L in alturas:
    l = L - L2PI
    delta = 2 * pi / l
    rho = l / (2 * pi)
    log10N = l / LN10 + log10(l - 1)
    log10_smin = (log10(mpf(9) / pi ** 2) - log10N) / 3
    log10_lam = 2 * (log10_smin + log10(delta)) - log10(2)
    sstar = sqrt(2 * RECORDE) / delta
    frac = mpf(1) if sstar > 50 else erf(2 * sstar / sqrt(pi)) - (4 * sstar / pi) * exp(-4 * sstar ** 2 / pi)
    altura_entre = 1 / (rho * frac)
    lnL = log(L)
    w = max(1 / (mpf("5.558691") * L), 1 / (mpf("55.241") * L ** (mpf(2) / 3) * lnL ** (mpf(1) / 3)))
    out.append({"altura": nome, "log10_N": float(log10N) if log10N < 1e300 else str(mp.nstr(log10N, 6)),
                "espacamento": float(delta) if delta > 1e-300 else str(mp.nstr(delta, 6)),
                "menos_log10_lambda_min": float(-log10_lam) if -log10_lam < 1e300 else str(mp.nstr(-log10_lam, 6)),
                "s_do_recorde": float(sstar) if sstar < 1e300 else str(mp.nstr(sstar, 6)),
                "fracao_mais_frageis_que_o_recorde": float(frac),
                "altura_media_entre_eles": float(altura_entre) if altura_entre > 1e-300 else str(mp.nstr(altura_entre, 6)),
                "w_sem_zeros": float(w) if w > 1e-300 else str(mp.nstr(w, 6)),
                "b_max": str(mp.nstr(mpf(1) / 2 - w, 12))})
json.dump(out, open("acima.json", "w"), ensure_ascii=False, indent=1)
for r in out:
    print(r["altura"].ljust(12), str(r["menos_log10_lambda_min"])[:14].ljust(15), "%.3g" % r["fracao_mais_frageis_que_o_recorde"],
          str(r["altura_media_entre_eles"])[:12].ljust(13), str(r["w_sem_zeros"])[:12])
