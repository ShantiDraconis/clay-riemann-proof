"""Todos os zeros da zeta de Fibonacci Σ F_n^{−s} em [−4,5; 1,5] × (0; 300], e como eles se ligam aos polos.

    python3 zeros_fibonacci.py      (grava zeros_fibonacci.json; ~1 min)

Continuação estável em precisão dupla (a de Navas com n₀ = 1 perde todos os dígitos acima de t ≈ 60):

    ζ_F(s) = Σ_{n<n₀} F_n^{−s} + 5^{s/2} Σ_{k≥0} C(s+k−1, k)·x_k^{n₀}/(1 − x_k),   x_k = (−1)^k φ^{−s−2k},

com n₀ = 12 e 8 termos em k (porque F_n = φⁿ(1 − (−φ^{−2})ⁿ)/√5 e Σ_{n≥n₀} x_kⁿ = x_k^{n₀}/(1 − x_k)). Conferida contra
mpmath com 60 dígitos (tabela VALIDACAO). Polos onde x_k = 1: s = −2k + iπ(2m + [k ímpar])/log φ.

Busca: mínimos locais de |ζ_F| numa malha de passo 0,02, Newton, e conferência pelo princípio do argumento em 30
faixas de altura 10 (zeros − polos = número de voltas); onde falta zero, células de 0,5 × 1 com várias partidas.
"""
import json
import math

import numpy as np

LP = math.log((1 + 5 ** 0.5) / 2)
P = 2 * math.pi / LP                     # o período de φ^{−s} em t
F = [1, 1]
while len(F) < 60:
    F.append(F[-1] + F[-2])
S0, S1, T1 = -4.5, 1.5, 300.0
# valores de referência (mpmath, 60 dígitos, continuação de Navas)
VALIDACAO = [(2, 2.42632075117), (0.4 + 25.6967j, -0.137202222945 - 0.116384632301j),
             (-2 + 100j, 14.6400079548 + 4.77462392651j), (-3 + 150j, 276.22480941 - 3.27482512159j),
             (0.2 + 150j, 0.150205119983 - 0.708239698401j), (-0.5 + 300j, 13.1717160252 - 2.127356891j),
             (-4 + 300j, -3209.45868652 + 11184.1247206j)]


def zf(s, n0=12, K=8):
    s = np.asarray(s, dtype=complex)
    with np.errstate(all="ignore"):
        tot = np.zeros_like(s)
        for n in range(1, n0):
            tot = tot + np.exp(-s * math.log(F[n - 1]))
        cauda = np.zeros_like(s)
        binom = np.ones_like(s)
        for k in range(K):
            x = (-1) ** k * np.exp(-(s + 2 * k) * LP)
            cauda = cauda + binom * x ** n0 / (1 - x)
            binom = binom * (s + k) / (k + 1)
        return tot + np.exp(s / 2 * math.log(5)) * cauda


def polos():
    return [complex(-2 * k, (2 * m + (k % 2)) * math.pi / LP) for k in range(3) for m in range(40)
            if S0 < -2 * k < S1 and 0 < (2 * m + (k % 2)) * math.pi / LP < T1]


def newton(z, it=60):
    for _ in range(it):
        h = 1e-6
        f = zf(z)
        df = (zf(z + h) - zf(z - h)) / (2 * h)
        dz = f / df
        z = z - dz
    return z, dz


def volta(a, b, c, d, n):
    lados = [np.linspace(complex(a, c), complex(b, c), n), np.linspace(complex(b, c), complex(b, d), n),
             np.linspace(complex(b, d), complex(a, d), n), np.linspace(complex(a, d), complex(a, c), n)]
    with np.errstate(all="ignore"):
        return sum(np.sum(np.angle(zf(l)[1:] / zf(l)[:-1])) for l in lados) / (2 * math.pi)


def busca():
    sig = np.arange(S0, S1 + 1e-9, 0.02)
    zs = []

    def junta(ws):
        for w in ws:
            if S0 < w.real < S1 and 0 < w.imag <= T1 and all(abs(w - v) > 1e-4 for v in zs):
                zs.append(w)

    for t0 in np.arange(0, T1, 10.0):
        t = np.arange(t0 - 0.04, t0 + 10.04, 0.02)
        Sg, Tg = np.meshgrid(sig, t)
        A = np.abs(zf(Sg + 1j * Tg))
        A[~np.isfinite(A)] = np.inf
        m = np.ones_like(A, dtype=bool)
        for di in (-1, 0, 1):
            for dj in (-1, 0, 1):
                if di or dj:
                    m &= A <= np.roll(np.roll(A, di, 0), dj, 1)
        m[0, :] = m[-1, :] = m[:, 0] = m[:, -1] = False
        ii, jj = np.nonzero(m)
        z, dz = newton(Sg[ii, jj] + 1j * Tg[ii, jj])
        esc = (np.abs(zf(z + 0.05)) + np.abs(zf(z - 0.05)) + np.abs(zf(z + 0.05j)) + np.abs(zf(z - 0.05j))) / 4
        junta(z[(np.abs(zf(z)) < 1e-6 * esc) & (np.abs(dz) < 1e-6)])
    pl = polos()
    conf = []
    for c in np.arange(0.05, T1, 10.0):
        d = min(c + 10.0, T1)
        w = volta(S0, S1, c, d, 80000)
        npol = sum(1 for p in pl if c < p.imag < d)
        nz = sum(1 for z in zs if c < z.imag < d)
        if round(w) + npol != nz:              # procura o que falta, célula por célula
            for a in np.arange(S0, S1, 0.5):
                for cc in np.arange(c, d - 1e-9, 1.0):
                    w2 = volta(a + 1e-3, a + 0.5 + 1e-3, cc, cc + 1.0, 800)
                    np2 = sum(1 for p in pl if a + 1e-3 < p.real < a + 0.5 + 1e-3 and cc < p.imag < cc + 1.0)
                    nz2 = sum(1 for z in zs if a + 1e-3 < z.real < a + 0.5 + 1e-3 and cc < z.imag < cc + 1.0)
                    if round(w2) + np2 > nz2:
                        x0, y0 = np.meshgrid(np.linspace(a + 0.05, a + 0.45, 5), np.linspace(cc + 0.1, cc + 0.9, 5))
                        z2, dz2 = newton((x0 + 1j * y0).ravel())
                        junta([q for q, e in zip(z2, dz2) if abs(e) < 1e-6 and a < q.real < a + 0.5 + 2e-3
                               and cc < q.imag < cc + 1.0])
            nz = sum(1 for z in zs if c < z.imag < d)
        conf.append({"faixa": [float(c), float(d)], "voltas": float(w), "polos": npol, "zeros": nz,
                     "confere": round(w) + npol == nz})
    zs.sort(key=lambda w: w.imag)
    return zs, pl, conf


def familias(zs, pl):
    """Companheiros dos polos de Re s = 0 (o zero mais perto de cada polo t = mP) e as cadeias à esquerda
    (zeros com Re < −1,5 ligados de período em período)."""
    z = np.array(zs)
    comp = []
    for p in sorted([q for q in pl if q.real == 0], key=lambda q: q.imag):
        j = int(np.argmin(np.abs(z - p)))
        comp.append({"m": int(round(p.imag / P)), "polo_t": p.imag, "zero": [z[j].real, z[j].imag],
                     "distancia": float(abs(z[j] - p)), "m_mod_3": int(round(p.imag / P)) % 3})
    esq = sorted([w for w in zs if w.real < -1.5], key=lambda w: w.imag)
    cadeias = []
    for w in esq:
        for c in cadeias:
            u = c[-1]
            if abs((w.imag - u.imag) - P) < 0.25 * P and abs(w.real - u.real) < 0.8:
                c.append(w)
                break
        else:
            cadeias.append([w])
    return comp, [[[w.real, w.imag] for w in c] for c in cadeias]


def main():
    erros = [abs(zf(np.array([s]))[0] - v) / abs(v) for s, v in VALIDACAO]
    zs, pl, conf = busca()
    comp, cadeias = familias(zs, pl)
    re = np.array([w.real for w in zs])
    fase = np.array([(w.imag % P) / P for w in zs])
    # cota: para Re s ≥ σ*, |ζ_F| ≥ 2 − Σ_{n≥3} F_n^{−σ} > 0, com σ* a raiz de Σ_{n≥3} F_n^{−σ} = 2
    a, b = 0.5, 1.0
    for _ in range(60):
        m = (a + b) / 2
        if sum(f ** -m for f in F[2:]) > 2:
            a = m
        else:
            b = m
    r = math.log(math.sqrt(5)) / LP
    out = {
        "validacao_erro_relativo_max": max(erros), "periodo_P": P, "zeros": [[w.real, w.imag] for w in zs],
        "n_zeros": len(zs), "polos": [[p.real, p.imag] for p in pl], "conferencia": conf,
        "faixas_conferidas": sum(1 for c in conf if c["confere"]), "re_max": float(re.max()), "re_min": float(re.min()),
        "sigma_estrela_sem_zeros_a_direita": b, "zeros_por_periodo": len(zs) / (T1 / P),
        "zeros_por_periodo_em_0_1": float(((re > 0) & (re < 1)).sum() / (T1 / P)),
        "companheiros": comp, "cadeias": cadeias,
        "giro_por_periodo_log_raiz5_sobre_log_phi": r, "giro_fracao": r % 1,
        "convergentes": ["2/1", "5/3", "97/58", "199/119"], "phi5": ((1 + 5 ** 0.5) / 2) ** 5, "raiz5_cubo": 5 ** 1.5,
        "fase_por_banda": {f"{a_}..{b_}": sorted(np.round(fase[(re >= a_) & (re < b_)], 3).tolist())
                           for a_, b_ in ((-4.5, -1.5), (-1.5, 0.0), (0.0, 0.75))},
    }
    json.dump(out, open("zeros_fibonacci.json", "w"), indent=1, ensure_ascii=False)
    print("validação: erro relativo máximo", max(erros))
    print("zeros:", len(zs), "faixas conferidas:", out["faixas_conferidas"], "de", len(conf), "| Re de",
          round(re.min(), 3), "a", round(re.max(), 3), "| σ* =", round(b, 4))
    print("companheiros (m, Re, dist):", [(c["m"], round(c["zero"][0], 3), round(c["distancia"], 2)) for c in comp])
    print("cadeias à esquerda:", [[(round(x, 2), round(y, 1)) for x, y in c] for c in cadeias if len(c) > 2])


if __name__ == "__main__":
    main()
