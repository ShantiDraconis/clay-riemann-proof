"""Quanto o método de 2026 dá se a correlação de pares for conhecida até o alcance A.

    python3 curva.py      (grava curva.json; ~1 min)

O método (Lamzouri 2026, Prop. 2.1 e Lema 3.2): para η real, par, com suporte em (−A/2, A/2) e ∫η² = 1, seja
g = η² (uma densidade). A desigualdade de Bessel dá

    N₀ˢ(T) ≥ 2N(T) − Σ_{γ,γ'} K(γ − γ')²,

e a correlação de pares de Montgomery, na forma (incondicional para A = 1)

    Σ ≈ N(T)·( Q(0) + ∫ min(|α|, 1)·Q(α) dα ),   Q = g * g,

transforma isso em N₀ˢ/N ≥ 2 − C, com

    C(g) = ‖g‖² + E min(|X − Y|, 1)   (X, Y independentes com densidade g)
         = 1 + ‖g‖² − ⟨g, Tri g⟩,      Tri(t) = (1 − |t|)₊.

Hoje só se conhece A = 1 (suporte de Q em [−1, 1]); aí o mínimo é C_MT = ½ + (1/√2)·cot(1/√2) (Montgomery–Taylor;
ótimo por Carneiro–Chandee–Littmann–Milinovich) e sai 0,6725. Para A > 1 a conta usa o valor conjecturado
F(α) = 1 em 1 ≤ |α| ≤ A (a conjectura de correlação de pares até A, aqui "CP(A)").

Cálculo: g constante por partes em n células de [−A/2, A/2] (g = c_i/h na célula i, Σ c_i = 1). Com
Φ(t) = t²/2 − |t|³/6 (|t| ≤ 1), |t|/2 − 1/6 (|t| ≥ 1), Φ'' = Tri, a integral de Tri numa célula × célula é exata:
M_ij = Φ(d + h) − 2Φ(d) + Φ(d − h), d = (i − j)h. Então m = ‖g‖² − ⟨g, Tri g⟩ = cᵀ(I/h − M/h²)c, minimizado com
Σc = 1 (o mínimo sai com c > 0, então é viável). Cada g constante por partes é admissível (a menos do ε da
suavização do Lema 3.2), então todo valor aqui é uma cota válida sob CP(A); o ótimo verdadeiro é um pouco maior.

Resultados: P(A) = 1 − m (simples e na reta), 1 − m/2 (distintos), 1 − 2m/(3 + 2√2) (simples ou na reta).
Com g uniforme, m = 1/(3A²) exatamente: P ≥ 1 − 1/(3A²).
"""
import json
import math
from fractions import Fraction as Fr

import numpy as np

R2 = math.sqrt(2)
C_MT = 0.5 + (1 / R2) / math.tan(1 / R2)


def phi(t):
    t = np.abs(t)
    return np.where(t <= 1, t ** 2 / 2 - t ** 3 / 6, t / 2 - 1 / 6)


def otimo(A, n):
    h = A / n
    d = (np.arange(n)[:, None] - np.arange(n)[None, :]) * h
    M = phi(d + h) - 2 * phi(d) + phi(d - h)
    B = np.eye(n) / h - M / h ** 2
    B = (B + B.T) / 2
    c = np.linalg.solve(B, np.ones(n))
    c /= c.sum()
    return float(c @ B @ c), c


def phi_exato(t):
    t = abs(t)
    return t * t / 2 - t ** 3 / 6 if t <= 1 else t / 2 - Fr(1, 6)


def m_exato(A, c_float, den=10 ** 9):
    """m(c) em racionais: arredonda c, renormaliza para Σc = 1 exatamente, e soma tudo em Fraction."""
    A = Fr(A).limit_denominator(1000)
    n = len(c_float)
    c = [Fr(round(x * den), den) for x in c_float]
    s = sum(c)
    c = [x / s for x in c]
    h = A / n
    Md = {}
    for k in range(-(n - 1), n):
        d = k * h
        Md[k] = phi_exato(d + h) - 2 * phi_exato(d) + phi_exato(d - h)
    quad = sum(x * x for x in c) / h
    cross = Fr(0)
    for i in range(n):
        ci = c[i]
        if ci == 0:
            continue
        cross += ci * sum(Md[i - j] * c[j] for j in range(n))
    return quad - cross / (h * h)


def P(m):
    return {"simples_e_na_reta": 1 - m, "distintos": 1 - m / 2, "simples_ou_na_reta": 1 - 2 * m / (3 + 2 * R2)}


def limiar(alvo, n_por_unidade=200):
    lo, hi = 1.0, 20.0
    for _ in range(40):
        mid = (lo + hi) / 2
        m, _ = otimo(mid, max(200, int(n_por_unidade * mid)))
        if 1 - m >= alvo:
            hi = mid
        else:
            lo = mid
    return hi


def main():
    val = {n: 1 - otimo(1.0, n)[0] for n in (100, 200, 400, 800)}
    As = [1.0, 1.1, 1.2, 1.25, 1.3, 1.4, 1.5, 1.75, 2.0, 2.5, 3.0, 3.5, 4.0, 5.0, 6.0, 8.0, 10.0]
    curva = []
    for A in As:
        m, c = otimo(A, max(400, int(300 * A)))
        curva.append({"A": A, "m": m, "uniforme_m": 1 / (3 * A * A), **P(m),
                      "uniforme_simples_e_na_reta": 1 - 1 / (3 * A * A)})
    exatos = []
    for A in (1.0, 1.5, 2.0, 3.0):
        m, c = otimo(A, 160)
        me = m_exato(A, c)
        exatos.append({"A": A, "n": 160, "m_racional_float": float(me), "P_racional": float(1 - me),
                       "m_racional": f"{me.numerator}/{me.denominator}" if me.denominator < 10 ** 60 else None})
    alvos = [0.70, 0.75, 0.80, 0.85, 0.90, 0.95, 0.99, 0.999]
    lim = {f"{a:.3f}": limiar(a) for a in alvos}
    out = {
        "C_MT": C_MT, "C0_hoje": 2 - C_MT, "C1_hoje": (3 - C_MT) / 2,
        "C2_hoje": (5 + 2 * R2 - 2 * C_MT) / (3 + 2 * R2),
        "validacao_A1": {str(k): v for k, v in val.items()},
        "curva": curva, "exatos_em_racionais": exatos, "alcance_necessario": lim,
    }
    json.dump(out, open("curva.json", "w"), indent=1, ensure_ascii=False)
    print(f"C_MT = {C_MT:.10f}; hoje: {2 - C_MT:.6f} (simples e na reta)")
    print("validação A = 1:", {k: round(v, 8) for k, v in val.items()})
    for r in curva:
        print(f"A = {r['A']:5.2f}: simples e na reta {r['simples_e_na_reta']:.5f} | distintos {r['distintos']:.5f} | "
              f"simples ou na reta {r['simples_ou_na_reta']:.5f} | g uniforme {r['uniforme_simples_e_na_reta']:.5f}")
    print("exatos (racionais):", [(e["A"], round(e["P_racional"], 7)) for e in exatos])
    print("alcance A necessário:", {k: round(v, 3) for k, v in lim.items()})


if __name__ == "__main__":
    main()
