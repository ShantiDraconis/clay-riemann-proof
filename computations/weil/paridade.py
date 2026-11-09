"""O passo que falta para (A): o menor autovalor de Weil é simples e o seu autovetor é par?

    python3 paridade.py n dígitos L1 L2 ...      (grava paridade_<L>.json)

O teorema de Connes–van Suijlekom (Commun. Math. Phys. 2025; Teorema 6.1 em Connes, arXiv 2602.04022) dá zeros reais
para a transformada do estado fundamental desde que o mínimo do espectro seja um autovalor simples com autofunção par.
Connes (§6.6) lista isso como passo em aberto para a forma de Weil. Aqui se mede o menor autovalor nos dois setores:

* par:   base cos(πjx/L), j = 0..n−1 (a mesma de alta.py);
* ímpar: base sin(πjx/L), j = 1..n.

Para g real, h = g ⋆ g̃ é sempre par, então o arquimediano e os primos têm a mesma fórmula nos dois setores. Só o termo
do polo muda de sinal: φ(i/2) + φ(−i/2) = 2ĝ(i/2)ĝ(−i/2), que é +2G² para g par e −2G² para g ímpar, com
G = ∫ g(x)e^{x/2} dx. Se o menor autovalor ímpar ficar acima de μ₁ e μ₁ < μ₂, o mínimo global é simples e par.
"""
import json
import sys

import mpmath as mp

from alta import I_cos, mangoldt


def h_impar(ai, aj, L, x):
    """∫ sin(a_i y)·sin(a_j (y − x)) dy sobre y ∈ [x − L, L] (0 ≤ x ≤ 2L)."""
    lo, hi = x - L, L
    return (I_cos(ai - aj, aj * x, lo, hi) - I_cos(ai + aj, -aj * x, lo, hi)) / 2


def h_par(ai, aj, L, x):
    lo, hi = x - L, L
    return (I_cos(ai + aj, -aj * x, lo, hi) + I_cos(ai - aj, aj * x, lo, hi)) / 2


def matriz(L, n, paridade, grau=8):
    L = mp.mpf(L)
    if paridade == "par":
        a = [mp.pi * j / L for j in range(n)]
        D = [2 * L if j == 0 else L for j in range(n)]
        h = h_par
        sinal = 1
    else:
        a = [mp.pi * j / L for j in range(1, n + 1)]
        D = [L] * n
        h = h_impar
        sinal = -1
    G = []
    for aj in a:
        z = mp.mpf(1) / 2 + 1j * aj
        w = (mp.exp(z * L) - mp.exp(-z * L)) / z                  # ∫ e^{iax} e^{x/2} dx
        G.append(mp.re(w) if paridade == "par" else mp.im(w))     # ∫ cos(ax)e^{x/2} ou ∫ sin(ax)e^{x/2}
    gl = mp.calculus.quadrature.GaussLegendre(mp.mp)
    nos = gl.calc_nodes(grau, mp.mp.prec)
    xs = [(t + 1) * L for t, _ in nos]
    ws = [w * L for _, w in nos]
    pesoA = [ws[q] * 2 * mp.exp(-xs[q] / 2) / (1 - mp.exp(-2 * xs[q])) for q in range(len(xs))]
    N = int(mp.floor(mp.exp(2 * L)))
    lam = mangoldt(max(N, 2))
    E1 = mp.e1(4 * L)
    M = mp.matrix(n, n)
    for i in range(n):
        for j in range(i, n):
            h0 = D[i] if i == j else mp.mpf(0)
            arch = h0 * E1
            for q in range(len(xs)):
                x = xs[q]
                hx = (h(a[i], a[j], L, x) + h(a[j], a[i], L, x)) / 2
                arch += ws[q] * h0 * mp.exp(-2 * x) / x - pesoA[q] * hx
            primos = mp.mpf(0)
            for m in range(2, N + 1):
                if lam[m]:
                    t = mp.log(m)
                    primos += mp.log(lam[m]) / mp.sqrt(m) * (h(a[i], a[j], L, t) + h(a[j], a[i], L, t)) / 2
            v = sinal * 2 * G[i] * G[j] - mp.log(mp.pi) * h0 + arch - 2 * primos
            M[i, j] = M[j, i] = v / mp.sqrt(D[i] * D[j])
    return M


if __name__ == "__main__":
    n = int(sys.argv[1])
    mp.mp.dps = int(sys.argv[2])
    for Ls in sys.argv[3:]:
        out = {"L": float(Ls), "n": n, "dps": mp.mp.dps}
        for p in ("par", "impar"):
            Ev = mp.eigsy(matriz(float(Ls), n, p), eigvals_only=True)
            E = sorted(Ev[k] for k in range(n))
            out[p] = [mp.nstr(x, 10) for x in E[:6]]
        out["minimo_global_par_e_simples"] = bool(mp.mpf(out["par"][0]) < mp.mpf(out["impar"][0])
                                                   and mp.mpf(out["par"][0]) < mp.mpf(out["par"][1]))
        json.dump(out, open(f"paridade_{Ls}.json", "w"), indent=1)
        print(f"L={Ls} n={n}: par {out['par'][:3]}   ímpar {out['impar'][:3]}   mínimo global simples e par: "
              f"{out['minimo_global_par_e_simples']}", flush=True)
