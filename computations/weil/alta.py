"""A forma de Weil em alta precisão (mpmath): a fronteira de (A) e a lei de (B).

    python3 alta.py n dígitos L1 L2 ...      (base com n funções; grava alta_<L>.json para cada escala)

Rodadas da §61: `36 60 0.6 0.7 0.8`, `32 70 0.9 1.0`, `40 90 1.1 1.2`, `44 110 1.2825`, `56 150 1.5` (≈ 5 a 15 min cada;
PYTHONPATH com o mpmath).

Tudo em forma fechada ou em quadratura de Gauss–Legendre de alta ordem, no espaço x (sem caudas oscilatórias):

    W(g) = 2·G(g)² − log π·h(0) + A(h) − 2 Σ_{n ≤ e^{2L}} Λ(n) n^{−½} h(log n),
    A(h) = ∫_0^{2L} [h(0)e^{−2x}/x − 2h(x)e^{−x/2}/(1 − e^{−2x})] dx + h(0)·E₁(4L),

com h = g ⋆ g, G(g) = ∫ g(x) e^{x/2} dx (g par). A fórmula de A vem de ψ(z) = ∫_0^∞ (e^{−t}/t − e^{−zt}/(1 − e^{−t})) dt e foi
conferida contra a integral em r com uma gaussiana (diferença 6·10⁻²⁰ a 30 dígitos).

Base: cos(πjx/L) em [−L, L], j = 0..n−1 (pares, ortogonais: Gram diagonal). h_ij em forma fechada.
Saída por escala: os menores autovalores; os zeros reais de ĝ* e o erro contra γ_k; a contagem de zeros de ĝ* no
retângulo [0,3; 70] × [−h, h], h = 1,5, 4 e 8 (princípio do argumento em precisão alta, adaptativo), contra as
trocas de sinal reais.
Os μ são cotas superiores de Rayleigh–Ritz para o mínimo verdadeiro na escala L (base finita).
"""
import json
import sys

import mpmath as mp

mp.mp.dps = 60


def mangoldt(N):
    lam = [0] * (N + 1)
    for p in range(2, N + 1):
        if all(p % q for q in range(2, int(p ** 0.5) + 1)):
            q = p
            while q <= N:
                lam[q] = p
                q *= p
    return lam


def I_cos(k, c, lo, hi):
    """∫_lo^hi cos(k y + c) dy."""
    if k == 0:
        return (hi - lo) * mp.cos(c)
    return (mp.sin(k * hi + c) - mp.sin(k * lo + c)) / k


def h_par(ai, aj, L, x):
    """∫ cos(a_i y)·cos(a_j (y − x)) dy sobre y ∈ [x − L, L] (0 ≤ x ≤ 2L)."""
    lo, hi = x - L, L
    return (I_cos(ai + aj, -aj * x, lo, hi) + I_cos(ai - aj, aj * x, lo, hi)) / 2


def matriz(L, n, grau=8):
    L = mp.mpf(L)
    a = [mp.pi * j / L for j in range(n)]
    D = [2 * L if j == 0 else L for j in range(n)]                                   # Gram diagonal
    G = []
    for j in range(n):
        z = mp.mpf(1) / 2 + 1j * a[j]
        G.append(mp.re((mp.exp(z * L) - mp.exp(-z * L)) / z))                       # ∫ cos(a x) e^{x/2} dx
    gl = mp.calculus.quadrature.GaussLegendre(mp.mp)
    nos = gl.calc_nodes(grau, mp.mp.prec)
    xs = [(t + 1) * L for t, _ in nos]                                               # [0, 2L]
    ws = [w * L for _, w in nos]
    pesoA = [ws[q] * 2 * mp.exp(-xs[q] / 2) / (1 - mp.exp(-2 * xs[q])) for q in range(len(xs))]
    # A(h) = h(0)·[∫ e^{−2x}/x dx + E1(4L)] − Σ_q pesoA_q h(x_q); o primeiro termo diverge sozinho, então junta-se
    # h(0) e h(x) nó a nó: ∫ [h(0)e^{−2x}/x − 2h(x)e^{−x/2}/(1−e^{−2x})] dx.
    N = int(mp.floor(mp.exp(2 * L)))
    lam = mangoldt(max(N, 2))
    M = mp.matrix(n, n)
    E1 = mp.e1(4 * L)
    for i in range(n):
        for j in range(i, n):
            h0 = D[i] if i == j else mp.mpf(0)
            arch = h0 * E1
            for q in range(len(xs)):
                x = xs[q]
                hx = (h_par(a[i], a[j], L, x) + h_par(a[j], a[i], L, x)) / 2
                arch += ws[q] * h0 * mp.exp(-2 * x) / x - pesoA[q] * hx
            primos = mp.mpf(0)
            for m in range(2, N + 1):
                if lam[m]:
                    t = mp.log(m)
                    ht = (h_par(a[i], a[j], L, t) + h_par(a[j], a[i], L, t)) / 2
                    primos += mp.log(lam[m]) / mp.sqrt(m) * ht
            v = 2 * G[i] * G[j] - mp.log(mp.pi) * h0 + arch - 2 * primos
            M[i, j] = M[j, i] = v / mp.sqrt(D[i] * D[j])
    return M, D, a, N


def ghat(c, a, L, r):
    s = mp.mpf(0)
    for cj, aj in zip(c, a):
        for k in (r - aj, r + aj):
            s += cj * (L if abs(k) < mp.mpf(10) ** (-40) else mp.sin(k * L) / k)
    return s


def conta_zeros_mp(f, lo, hi, h, passo=mp.mpf(1) / 10, tol=mp.mpf(1) / 2):
    """Número de zeros de f no retângulo [lo, hi] × [−h, h] (princípio do argumento, com subdivisão adaptativa: cada
    passo do contorno muda o argumento em menos de `tol`)."""
    cantos = [mp.mpc(lo, -h), mp.mpc(hi, -h), mp.mpc(hi, h), mp.mpc(lo, h), mp.mpc(lo, -h)]
    total = mp.mpf(0)
    for z0, z1 in zip(cantos[:-1], cantos[1:]):
        m = int(mp.ceil(abs(z1 - z0) / passo))
        pts = [z0 + (z1 - z0) * k / m for k in range(m + 1)]
        vals = [f(z) for z in pts]
        pilha = [(pts[k], pts[k + 1], vals[k], vals[k + 1], 0) for k in range(m)]
        while pilha:
            za, zb, fa, fb, d = pilha.pop()
            dz = mp.arg(fb / fa)
            if abs(dz) > tol and d < 40:
                zm = (za + zb) / 2
                fm = f(zm)
                pilha.append((za, zm, fa, fm, d + 1))
                pilha.append((zm, zb, fm, fb, d + 1))
            else:
                total += dz
    return total / (2 * mp.pi)


def analisa(L, n, grau=8, T=70):
    M, D, a, N = matriz(L, n, grau)
    E, Q = mp.eigsy(M)
    ordem = sorted(range(n), key=lambda k: E[k])
    mus = [E[k] for k in ordem[:6]]
    v = [Q[j, ordem[0]] for j in range(n)]
    c = [v[j] / mp.sqrt(D[j]) for j in range(n)]
    Lm = mp.mpf(L)
    # zeros reais
    grade = [mp.mpf(k) / 20 for k in range(10, 20 * T)]
    vals = [ghat(c, a, Lm, r) for r in grade]
    zs = []
    for k in range(len(grade) - 1):
        if vals[k] * vals[k + 1] < 0:
            zs.append(mp.findroot(lambda r: ghat(c, a, Lm, r), (grade[k], grade[k + 1]), solver="anderson"))
    gammas = []
    k = 1
    while True:
        g = mp.im(mp.zetazero(k))
        if g > T:
            break
        gammas.append(g)
        k += 1
    comp = []
    for g in gammas:
        z = min(zs, key=lambda q: abs(q - g)) if zs else None
        comp.append([float(g), mp.nstr(z - g, 5) if z is not None else None])
    # princípio do argumento em precisão alta (em precisão dupla ĝ* ~ Ξ(r) some no cancelamento acima de r ~ 40)
    # caixas de altura crescente: se a contagem não cresce com a altura, não há zeros complexos com |Im| ≤ 8 ali
    caixas = {h: conta_zeros_mp(lambda z: ghat(c, a, Lm, z), mp.mpf("0.3"), mp.mpf(T), mp.mpf(h)) for h in (1.5, 4, 8)}
    reais = sum(1 for z in zs if mp.mpf("0.3") < z < T)
    return {"L": float(L), "n": n, "grau": grau, "primos_ate": N, "mu": [mp.nstr(x, 8) for x in mus],
            "zeros_reais": [mp.nstr(z, 20) for z in zs], "erro_por_zero": comp,
            "retangulo": {"re": [0.3, T], "zeros_por_altura": {str(h): round(float(v), 6) for h, v in caixas.items()},
                          "reais": reais},
            "coeficientes": [mp.nstr(x, mp.mp.dps) for x in c]}


if __name__ == "__main__":
    n = int(sys.argv[1])
    mp.mp.dps = int(sys.argv[2])
    for Ls in sys.argv[3:]:
        r = analisa(float(Ls), n)
        r["dps"] = mp.mp.dps
        json.dump(r, open(f"alta_{Ls}.json", "w"), indent=1)
        print(f"L={Ls} n={n} primos≤{r['primos_ate']}: μ = {r['mu'][:4]}  retângulo: {r['retangulo']}")
        print("   erros:", [(round(g, 2), e) for g, e in r["erro_por_zero"][:14]])
