"""A refutação tendendo à prova: a família Z_t = ζ(s)L(s, χ₋₂₀) + t·L(s, χ₋₄)L(s, χ₅), de t = 1 a t = 0.

    python3 homotopia.py seguir > homotopia_seguir.json      (segue os 13 zeros fora da reta de t = 1 até a reta)
    python3 homotopia.py contar T > homotopia_contar_T.json  (princípio do argumento em t = T, 0,505 < Re s < 3)

As duas parcelas têm a mesma equação funcional, Λ(s) = (√20/2π)^s Γ(s)·(·), e coeficientes reais; então toda Z_t
com t real é simétrica por s ↦ 1 − s̄ (Analogs.Simetrica; Identidades.familia_simetrica). Em t = 1, Z_1 é a zeta de
Epstein de m² + 5n² (vezes 2): 13 pares fora da reta até Im 100 (README §39). Em t = 0, Z_0 = ζ_K(s), a zeta de
Dedekind de K = Q(√−5), produto de duas L-funções (para a qual a RH generalizada é conjectura, como para ζ).
Para cada zero fora da reta de Z_1 seguimos ρ(t) quando t desce: b(t) = Re ρ(t) − ½ vai a 0 num t_c, onde o par
encontra o espelho sobre a reta (zero duplo, κ = 0) e depois segue como dois zeros na reta. Perto de t_c,
b² ≈ C·(t − t_c) (a lei da raiz quadrada, a mesma do fluxo de de Bruijn). mpmath, 15 dígitos, sem certificação.
"""
import json
import math
import sys
from multiprocessing import Pool

sys.path.insert(0, "/home/claude/ext/mpmath")
from mpmath import mp, mpc, mpf, dirichlet, zeta, findroot

mp.dps = 15
CHI_4, LEG5 = [0, 1, 0, -1], [0, 1, -1, -1, 1]
CHI_20 = [CHI_4[n % 4] * LEG5[n % 5] for n in range(20)]


def A(s):
    return zeta(s) * dirichlet(s, CHI_20)


def B(s):
    return dirichlet(s, CHI_4) * dirichlet(s, LEG5)


def Z(t, s):
    return A(s) + t * B(s)


def raiz(t, s0):
    return findroot(lambda z: Z(t, z), (s0, s0 + mpf("0.001") + mpf("0.001") * 1j), solver="secant", tol=1e-24,
                    maxsteps=60)


def seguir(rho0):
    s = mpc(*rho0)
    t, h = 1.0, 0.02
    traj = [(1.0, float(s.real), float(s.imag))]
    while t > 0:
        tn = max(0.0, t - h)
        try:
            sn = raiz(tn, s)
        except Exception:
            h /= 2
            if h < 1e-6:
                break
            continue
        if abs(complex(sn - s)) > 0.25 or abs(complex(Z(tn, sn))) > 1e-8:
            h /= 2
            if h < 1e-6:
                break
            continue
        b = abs(float(sn.real) - 0.5)
        t, s = tn, sn
        traj.append((t, float(s.real), float(s.imag)))
        if b < 0.004:
            break
        # perto do encontro b² ≈ C(t − t_c): passo pequeno o bastante para não pular t_c
        if len(traj) >= 3:
            (t1, r1, _), (t2, r2, _) = traj[-2], traj[-1]
            b1, b2 = abs(r1 - 0.5), abs(r2 - 0.5)
            dC = (b1 * b1 - b2 * b2) / max(t1 - t2, 1e-12)
            if dC > 0:
                h = min(0.02, max(2e-5, 0.4 * b2 * b2 / dC))
    # ajuste b² = C(t − t_c) nos últimos pontos
    pts = [(tt, (r - 0.5) ** 2) for tt, r, _ in traj[-4:]]
    n = len(pts)
    mt = sum(p[0] for p in pts) / n
    mb = sum(p[1] for p in pts) / n
    var = sum((p[0] - mt) ** 2 for p in pts)
    C = sum((p[0] - mt) * (p[1] - mb) for p in pts) / var if var > 0 else float("nan")
    tc = mt - mb / C if C and C == C else float("nan")
    return {"rho_t1": list(rho0), "b_t1": rho0[0] - 0.5, "trajetoria": traj, "t_ultimo": t,
            "b_ultimo": abs(traj[-1][1] - 0.5), "gama_no_encontro": traj[-1][2], "t_c": tc, "C": C,
            "chegou_na_reta": abs(traj[-1][1] - 0.5) < 0.004}


def contar(T, X0=0.505, X1=3.0, TOPO=100):
    def f(s):
        return Z(T, s)

    def dang(a, b):
        r = complex(b) / complex(a)
        return math.atan2(r.imag, r.real)

    def seg(p, q, fp, fq, prof=0):
        d = dang(fp, fq)
        if abs(d) < 0.3 or prof > 22:
            return d, prof > 22
        m = (p + q) / 2
        fm = f(m)
        d1, e1 = seg(p, m, fp, fm, prof + 1)
        d2, e2 = seg(m, q, fm, fq, prof + 1)
        return d1 + d2, e1 or e2

    res = []
    y = 1.0
    while y < TOPO - 1e-9:
        y1 = min(y + 2, TOPO)
        cant = [mpc(X0, y), mpc(X1, y), mpc(X1, y1), mpc(X0, y1)]
        tot, ruim = 0.0, False
        for a, b in zip(cant, cant[1:] + cant[:1]):
            k = max(4, int(abs(complex(b - a)) / 0.1))
            ps = [a + (b - a) * j / k for j in range(k + 1)]
            vs = [f(p) for p in ps]
            for p, q, fp, fq in zip(ps, ps[1:], vs, vs[1:]):
                d, e = seg(p, q, fp, fq)
                tot += d
                ruim = ruim or e
        c = tot / (2 * math.pi)
        res.append({"Im_de": y, "Im_ate": y1, "zeros": round(c), "desvio": abs(c - round(c)), "suspeito": ruim})
        print(T, res[-1], file=sys.stderr, flush=True)
        y += 2
    return {"t": T, "Re": [X0, X1], "faixas": res, "total": sum(r["zeros"] for r in res),
            "desvio_max": max(r["desvio"] for r in res)}


if __name__ == "__main__":
    if sys.argv[1] == "seguir":
        fora = json.load(open("../aglomeracoes/analogos_fora.json"))["Epstein m²+5n²"]["zeros"]
        zs = sorted([(z["re"], z["im"]) for z in fora] + [(0.81117208120602838, 58.50773732773190)],
                    key=lambda z: z[1])
        with Pool(2) as pool:
            out = pool.map(seguir, zs)
        print(json.dumps({"familia": "Z_t = ζ L(χ₋₂₀) + t L(χ₋₄) L(χ₅)", "zeros": out}, ensure_ascii=False))
    else:
        print(json.dumps(contar(float(sys.argv[2])), ensure_ascii=False))
