"""A rota pelas grades em alta precisão (mpmath): B-splines cúbicos, queda estrita e zeros no círculo sem achar raízes.

    python3 grade_alta.py dígitos p L N1 N2 ...      (grava grade_alta_<L>_p<p>.json)

Base: φ_j(x) = N_p(x − jδ), B-splines de ordem p, passo δ = 2L/N, j = 0..N − p (todos com suporte em [0, 2L]). A forma
de Weil é invariante por translação, então a matriz T e a Gram G são de Toeplitz (ver grade.py para ⟨D, ·⟩). Com o
menor autovalor generalizado μ₁ (T ξ = μ₁ G ξ), M = T − μ₁G é de Toeplitz, semidefinida positiva e com ξ no núcleo.

Mede-se o que os teoremas do kernel pedem (`Grade.simples_de_queda`, `Toeplitz.zeros_no_circulo`):

* queda estrita: μ₁(seção sem a última função) > μ₁;
* zeros de P(z) = Σ ξ_j z^j no círculo, sem achar raízes: para ξ simétrico, z^{−c}P(e^{iθ}) = Q(θ) = Σ ξ_j cos((j − c)θ)
  é real (c = (M − 1)/2). Se Q troca de sinal ⌊(M − 1)/2⌋ vezes em (0, π), então, contando o grau, todos os M − 1 zeros
  de P estão no círculo;
* os zeros r_k = θ_k/δ contra os γ_k.
"""
import json
import sys

import mpmath as mp

from alta import mangoldt

GAMMAS = None


def Mq(q, x):
    """B-spline cardinal de ordem q em [0, q], ∫ = 1."""
    s = mp.mpf(0)
    for k in range(q + 1):
        y = x - k
        if y > 0:
            s += (-1) ** k * mp.binomial(q, k) * y ** (q - 1)
    return s / mp.factorial(q - 1)


def gauss(f, a, b, nos):
    m, h = (a + b) / 2, (b - a) / 2
    return h * mp.fsum(w * f(m + h * t) for t, w in nos)


def matrizes(L, N, p, nos):
    L = mp.mpf(L)
    d = 2 * L / N
    Mn = N - p + 1
    k = lambda x: d * Mq(2 * p, x / d + p)                        # autocorrelação de N_p
    lam = mangoldt(max(int(mp.floor(mp.exp(2 * L))), 2))
    peso = lambda x: mp.exp(-x / 2) / (1 - mp.exp(-2 * x))
    lap = d ** (2 - 2 * p) * (4 * mp.sinh(d / 4)) ** (2 * p)
    tau, G = [], []
    for m in range(Mn):
        km0 = k(m * d)
        G.append(km0)
        polo = 2 * mp.cosh(m * d / 2) * lap
        f = lambda x: km0 * mp.exp(-2 * x) / x - (k(x - m * d) + k(x + m * d)) * peso(x)
        arch = mp.fsum(gauss(f, i * d, (i + 1) * d, nos) for i in range(m + p)) + km0 * mp.e1(2 * (m + p) * d)
        primos = mp.fsum(mp.log(lam[n]) / mp.sqrt(n) * (k(mp.log(n) - m * d) + k(mp.log(n) + m * d))
                         for n in range(2, len(lam)) if lam[n])
        tau.append(polo - mp.log(mp.pi) * km0 + arch - primos)
    T = mp.matrix(Mn, Mn)
    Gm = mp.matrix(Mn, Mn)
    for i in range(Mn):
        for j in range(Mn):
            T[i, j] = tau[abs(i - j)]
            Gm[i, j] = G[abs(i - j)]
    return T, Gm, d


def menor(T, G):
    n = T.rows
    Lc = mp.cholesky(G)
    Li = mp.inverse(Lc)
    A = Li * T * Li.T
    A = (A + A.T) / 2
    E, Q = mp.eigsy(A)
    ordem = sorted(range(n), key=lambda i: E[i])
    y = mp.matrix([Q[i, ordem[0]] for i in range(n)])
    xi = Li.T * y
    return E[ordem[0]], E[ordem[1]], [xi[i] for i in range(n)]


def analisa(L, N, p, nos):
    T, G, d = matrizes(L, N, p, nos)
    n = T.rows
    mu1, mu2, xi = menor(T, G)
    sub = lambda X: mp.matrix([[X[i, j] for j in range(n - 1)] for i in range(n - 1)])
    mu1s, _, _ = menor(sub(T), sub(G))
    escala = max(abs(x) for x in xi)
    xi = [x / escala for x in xi]
    simetria = max(abs(xi[i] - xi[n - 1 - i]) for i in range(n))
    c = mp.mpf(n - 1) / 2
    Q = lambda th: mp.fsum(xi[j] * mp.cos((j - c) * th) for j in range(n))
    K = 40 * n
    ths = [mp.pi * (i + mp.mpf(1) / 2) / K for i in range(K)]
    vals = [Q(t) for t in ths]
    trocas = []
    for i in range(K - 1):
        if vals[i] * vals[i + 1] < 0:
            trocas.append(mp.findroot(Q, (ths[i], ths[i + 1]), solver="anderson"))
    esperado = (n - 1) // 2
    r = sorted(t / d for t in trocas)
    comp = []
    for g in GAMMAS:
        if r:
            z = min(r, key=lambda q: abs(q - g))
            comp.append([float(g), mp.nstr(z - g, 4)])
    return {"L": float(L), "N": N, "p": p, "funcoes": n, "passo": float(d), "dps": mp.mp.dps,
            "mu1": mp.nstr(mu1 / 1, 8), "mu2": mp.nstr(mu2, 8), "mu1_secao": mp.nstr(mu1s, 8),
            "queda_estrita": bool(mu1 < mu1s), "assimetria_de_xi": mp.nstr(simetria, 3),
            "trocas_em_0_pi": len(trocas), "esperado": esperado, "todos_no_circulo": len(trocas) == esperado,
            "zeros_r": [mp.nstr(x, 15) for x in r[:30]], "comparacao": comp[:12]}


if __name__ == "__main__":
    mp.mp.dps = int(sys.argv[1])
    p = int(sys.argv[2])
    L = sys.argv[3]
    GAMMAS = [mp.im(mp.zetazero(k)) for k in range(1, 13)]
    gl = mp.calculus.quadrature.GaussLegendre(mp.mp)
    nos = gl.calc_nodes(4, mp.mp.prec)
    out = []
    for Ns in sys.argv[4:]:
        a = analisa(L, int(Ns), p, nos)
        out.append(a)
        print(f"L={L} p={p} N={Ns} ({a['funcoes']} funções): μ₁={a['mu1']} seção={a['mu1_secao']} μ₂={a['mu2']} "
              f"queda={a['queda_estrita']} trocas={a['trocas_em_0_pi']}/{a['esperado']} assim={a['assimetria_de_xi']} "
              f"erros={[e for _, e in a['comparacao'][:6]]}", flush=True)
        json.dump(out, open(f"grade_alta_{L}_p{p}.json", "w"), indent=1)
