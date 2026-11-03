"""Zeros fora da reta crítica de funções com equação funcional e SEM produto de Euler (onde RH falha).

    python3 analogos_fora.py [nome ...]   (grava analogos_fora.json depois de cada função)

* Davenport–Heilbronn: f = ((1 − iκ)/2) L(s, χ) + ((1 + iκ)/2) L(s, χ̄), χ mod 5 com χ(2) = i,
  κ = (√(10 − 2√5) − 2)/(√5 − 1);
* Epstein da forma m² + 5n² (classe 2, discriminante −20): Z = ζ(s) L(s, χ₋₂₀) + L(s, χ₋₄) L(s, χ₅);
* ζ(s) + ζ(s + 1) (sem equação funcional de ζ; soma quebra o produto de Euler).
Malha em Re ∈ [0,52; 1,3] (Re ∈ [−0,46; 1,3] para ζ(s)+ζ(s+1), que não tem simetria), 1 ≤ Im ≤ 170 (Davenport–Heilbronn) ou 100 (as outras), mínimos locais de |f| refinados por findroot (secante complexa); só ficam
raízes com |f| < 10⁻¹² e |Re − ½| > 10⁻⁶.
"""
import json
import sys
from multiprocessing import Pool

sys.path.insert(0, "/home/claude/ext/mpmath")
from mpmath import mp, mpf, mpc, sqrt, dirichlet, zeta, findroot

kap = (sqrt(10 - 2 * sqrt(5)) - 2) / (sqrt(5) - 1)
CHI5 = [0, 1, 1j, -1j, -1]
CHI5B = [0, 1, -1j, 1j, -1]
CHI_4 = [0, 1, 0, -1]
LEG5 = [0, 1, -1, -1, 1]
CHI_20 = [CHI_4[n % 4] * LEG5[n % 5] for n in range(20)]


def dh(s):
    return (1 - 1j * kap) / 2 * dirichlet(s, CHI5) + (1 + 1j * kap) / 2 * dirichlet(s, CHI5B)


def epstein(s):
    return zeta(s) * dirichlet(s, CHI_20) + dirichlet(s, CHI_4) * dirichlet(s, LEG5)


def zz(s):
    return zeta(s) + zeta(s + 1)


F = {"Davenport–Heilbronn": dh, "Epstein m²+5n²": epstein, "ζ(s)+ζ(s+1)": zz}
RES = [0.52 + 0.06 * i for i in range(14)]
RES_SEM_SIMETRIA = [-0.46 + 0.06 * i for i in range(30)]  # ζ(s)+ζ(s+1) não tem simetria em torno de ½
TOPO = {"Davenport–Heilbronn": 170, "Epstein m²+5n²": 100, "ζ(s)+ζ(s+1)": 100}
IMS = [1 + 0.2 * j for j in range(846)]


def grade_re(nome):
    return RES_SEM_SIMETRIA if nome == "ζ(s)+ζ(s+1)" else RES


def linha(args):
    nome, x = args
    mp.dps = 15
    f = F[nome]
    return [abs(f(mpc(x, y))) if y <= TOPO[nome] else mpf(1e9) for y in IMS]


def refina(args):
    nome, x, y = args
    mp.dps = 30
    f = F[nome]
    try:
        r = findroot(f, (mpc(x, y), mpc(x + 0.01, y + 0.01)), solver="secant", tol=mpf(10) ** -25, maxsteps=60)
    except Exception:
        return None
    if abs(f(r)) < 1e-12 and abs(r.real - 0.5) > 1e-6 and 0 < r.imag < 175:
        return (float(r.real), float(r.imag), float(abs(f(r))))
    return None


if __name__ == "__main__":
    out = json.load(open("analogos_fora.json")) if len(sys.argv) > 1 else {}
    with Pool(2) as pool:
        for nome in (sys.argv[1:] or list(F)):
            RS = grade_re(nome)
            grade = pool.map(linha, [(nome, x) for x in RS])
            cand = []
            for i in range(len(RS)):
                for j in range(len(IMS)):
                    v = grade[i][j]
                    viz = [grade[a][b] for a in (i - 1, i, i + 1) for b in (j - 1, j, j + 1)
                           if 0 <= a < len(RS) and 0 <= b < len(IMS) and (a, b) != (i, j)]
                    if all(v <= w for w in viz) and v < 0.5:
                        cand.append((nome, RS[i], IMS[j]))
            raizes = [r for r in pool.map(refina, cand) if r]
            uniq = []
            for r in sorted(raizes):
                if not any(abs(r[0] - u[0]) < 1e-8 and abs(r[1] - u[1]) < 1e-8 for u in uniq):
                    uniq.append(r)
            out[nome] = {"ate_Im": TOPO[nome],
                         "zeros": [{"re": r[0], "im": r[1], "b": abs(r[0] - 0.5), "abs_f": r[2]} for r in uniq]}
            print(nome, len(cand), "candidatos,", len(uniq), "fora da reta", file=sys.stderr)
            with open("analogos_fora.json", "w") as fh:          # grava a cada função
                json.dump(out, fh, ensure_ascii=False, indent=1)
