"""φ, Fibonacci, 1/√p e os quartetos: onde a razão áurea entra de fato na zeta, e se zeros fora da reta seguem φ.

    python3 aurea.py        (grava aurea.json; ~1 min)

1. Os quartetos fora da reta que EXISTEM (zeta de Epstein de m² + 5n² e função de Davenport–Heilbronn, dados da §39 em
   ../parametro/): forma (retângulo de lados 2b e 2γ), ângulo da diagonal em frações de π, imagem no círculo de Li, e
   o teste "seguem φ?": partes fracionárias de log_φ(γ/b), log_φ(2b) e razões γ_{k+1}/γ_k contra o uniforme.
2. φ dentro de uma L de Riemann: Q(√5) tem ζ_K = ζ·L(s, χ₅) e unidade fundamental φ, logo
   L(1, χ₅) = 2·log φ/√5 (fórmula do número de classes). Os primeiros zeros de L(s, χ₅) e a contagem pelo princípio do
   argumento (estão na reta?).
3. A zeta de Fibonacci Σ F_n^{−s} (sem produto de Euler, sem equação funcional): continuação de Navas (2001),
   polos em s = −2k + iπ(2m + [k ímpar])/log φ, e onde ficam os seus zeros.
4. A lei de entrada: p | F_{p − (5/p)} (o fator de Euler de L(s, χ₅) decide onde p entra em Fibonacci).
5. Frações: F_{n+1}/F_n → φ, e F_n²·|φ − F_{n+1}/F_n| → 1/√5 (a constante de Hurwitz), que é |5^{−s}| na reta.
Ponto flutuante (não certificado); as identidades exatas estão no kernel (`ClayRiemannProof/Aurea.lean`).
"""
import json
import math

import numpy as np
from scipy.special import digamma, loggamma

from zeta_em import COEF

PHI = (1 + 5 ** 0.5) / 2
LPHI = math.log(PHI)


def quartetos():
    out = {}
    for nome, arq in (("Epstein m²+5n²", "../parametro/epstein.json"), ("Davenport–Heilbronn", "../parametro/dh.json")):
        d = json.load(open(arq))
        lista = []
        for z in d["em_volta_dos_fora"]:
            sig, gam = z["rho"]
            b = sig - 0.5
            rho = complex(sig, gam)
            w1, w2 = 1 - 1 / rho, 1 - 1 / complex(1 - sig, gam)
            theta = math.atan2(gam, b)
            lista.append({
                "b": b, "gama": gam, "lados": [2 * b, 2 * gam], "razao_gama_b": gam / b,
                "angulo_diagonal_sobre_pi": theta / math.pi, "falta_para_meio": 0.5 - theta / math.pi,
                "falta_vezes_pi_gama_sobre_b": (0.5 - theta / math.pi) * math.pi * gam / b,
                "li": {"abs_w_rho": abs(w1), "abs_w_1_menos_rho_barra": abs(w2),
                       "produto": abs(w1) * abs(w2), "arg_sobre_pi": math.atan2(w1.imag, w1.real) / math.pi,
                       "defeito_2b_sobre_rho2": 2 * b / abs(rho) ** 2, "1_menos_abs_w2": 1 - abs(w1) ** 2},
                "frac_logphi_razao": (math.log(gam / b) / LPHI) % 1, "frac_logphi_2b": (math.log(2 * b) / LPHI) % 1,
            })
        gs = [q["gama"] for q in lista]
        out[nome] = {"quartetos": lista, "razoes_alturas": [gs[k + 1] / gs[k] for k in range(len(gs) - 1)]}
    # teste "seguem φ": as frações de log_φ deveriam se acumular em 0 (ou 1); KS contra o uniforme
    todos = [q for v in out.values() for q in v["quartetos"]]
    fr = sorted(q["frac_logphi_razao"] for q in todos)
    fr2 = sorted(q["frac_logphi_2b"] for q in todos)

    def ks(xs):
        n = len(xs)
        return max(max((i + 1) / n - x, x - i / n) for i, x in enumerate(xs))

    dist0 = [min(x, 1 - x) for x in fr]
    razoes = [r for v in out.values() for r in v["razoes_alturas"]]
    out["teste_phi"] = {
        "n": len(todos), "ks_frac_logphi_razao": ks(fr), "ks_frac_logphi_2b": ks(fr2),
        "ks_critico_5pc": 1.36 / math.sqrt(len(todos)),
        "distancia_media_a_potencia_de_phi": sum(dist0) / len(dist0), "esperado_se_uniforme": 0.25,
        "razoes_alturas_perto_de_phi": sum(1 for r in razoes if abs(r - PHI) < 0.05), "razoes_total": len(razoes),
    }
    return out


def L1_chi5():
    chi = {1: 1, 2: -1, 3: -1, 4: 1}
    L1 = -sum(c * digamma(a / 5) for a, c in chi.items()) / 5
    return {"L1_digamma": L1, "dois_log_phi_sobre_raiz5": 2 * LPHI / math.sqrt(5), "diferenca": L1 - 2 * LPHI / math.sqrt(5)}


def hurwitz(s, a, N=40, M=12):
    s = np.asarray(s, dtype=complex)
    n = np.arange(N, dtype=float) + a
    tot = np.exp(-np.multiply.outer(s, np.log(n))).sum(axis=-1)
    x = N + a
    lx = math.log(x)
    tot = tot + np.exp((1 - s) * lx) / (s - 1) + 0.5 * np.exp(-s * lx)
    poch, pot = s.copy(), np.exp(-(s + 1) * lx)
    for k in range(1, M + 1):
        tot = tot + COEF[k - 1] * poch * pot
        poch = poch * (s + 2 * k - 1) * (s + 2 * k)
        pot = pot / (x * x)
    return tot


def L_chi5(s):
    s = np.asarray(s, dtype=complex)
    chi = {1: 1, 2: -1, 3: -1, 4: 1}
    return np.exp(-s * math.log(5)) * sum(c * hurwitz(s, a / 5) for a, c in chi.items())


def zeros_L(T=40.0):
    t = np.linspace(0.5, T, 40000)
    s = 0.5 + 1j * t
    th = (t / 2) * math.log(5 / math.pi) + np.imag(loggamma(s / 2))
    Z = np.real(np.exp(1j * th) * L_chi5(s))
    zs = []
    for k in range(len(t) - 1):
        if Z[k] == 0 or Z[k] * Z[k + 1] < 0:
            a, b = t[k], t[k + 1]
            for _ in range(50):
                m = (a + b) / 2
                zm = np.real(np.exp(1j * ((m / 2) * math.log(5 / math.pi) + np.imag(loggamma((0.5 + 1j * m) / 2))))
                             * L_chi5(np.array([0.5 + 1j * m]))[0])
                za = np.real(np.exp(1j * ((a / 2) * math.log(5 / math.pi) + np.imag(loggamma((0.5 + 1j * a) / 2))))
                             * L_chi5(np.array([0.5 + 1j * a]))[0])
                if za * zm <= 0:
                    b = m
                else:
                    a = m
            zs.append((a + b) / 2)
    # princípio do argumento no retângulo [0,02; 0,98] × [1; T]
    lados = [np.linspace(0.02 + 1j, 0.98 + 1j, 4000), np.linspace(0.98 + 1j, 0.98 + 1j * T, 40000),
             np.linspace(0.98 + 1j * T, 0.02 + 1j * T, 4000), np.linspace(0.02 + 1j * T, 0.02 + 1j, 40000)]
    ang = 0.0
    for lado in lados:
        v = L_chi5(lado)
        ang += np.sum(np.angle(v[1:] / v[:-1]))
    dentro = ang / (2 * math.pi)
    return {"zeros_na_reta": zs, "n_na_reta_1_a_T": sum(1 for z in zs if z > 1), "argumento_conta": dentro, "T": T}


def zeta_fib(s, K=80):
    s = np.asarray(s, dtype=complex)
    with np.errstate(all="ignore"):
        return _zeta_fib(s, K)


def _zeta_fib(s, K):
    tot = np.zeros_like(s)
    binom = np.ones_like(s)          # C(s+k−1, k)
    for k in range(K):
        x = (-1) ** k * np.exp(-(s + 2 * k) * LPHI)
        tot = tot + binom * x / (1 - x)
        binom = binom * (s + k) / (k + 1)
    return np.exp(s / 2 * math.log(5)) * tot


def _winding(a, b, c, d, n=400):
    lados = [np.linspace(complex(a, c), complex(b, c), n), np.linspace(complex(b, c), complex(b, d), n),
             np.linspace(complex(b, d), complex(a, d), n), np.linspace(complex(a, d), complex(a, c), n)]
    ang = 0.0
    for lado in lados:
        v = zeta_fib(lado, K=120)
        ang += np.sum(np.angle(v[1:] / v[:-1]))
    return ang / (2 * math.pi)


def zeros_fib(S0=-3.5, S1=3.0, T0=0.1, T1=45.0):
    """Zeros de ζ_F no retângulo [S0, S1] × [T0, T1]: células 0,5 × 1 com número de voltas (+ polos conhecidos) e
    Newton a partir do centro; a soma confere com o princípio do argumento no retângulo inteiro."""
    fibs = [1, 1]
    while len(fibs) < 200:
        fibs.append(fibs[-1] + fibs[-2])
    direto = sum(1 / f ** 2 for f in fibs)
    polos = [complex(-2 * k, (2 * m + (k % 2)) * math.pi / LPHI) for k in range(0, 3) for m in range(0, 10)]
    dentro = lambda z, a, b, c, d: a < z.real < b and c < z.imag < d
    zs = []
    for a in np.arange(S0, S1 - 1e-9, 0.5):
        for c in np.arange(T0, T1 - 1e-9, 1.0):
            nz = round(_winding(a, a + 0.5, c, c + 1.0)) + sum(1 for p in polos if dentro(p, a, a + 0.5, c, c + 1.0))
            if nz > 0:
                z = complex(a + 0.25, c + 0.5)
                for _ in range(100):
                    f = zeta_fib(np.array([z]), K=120)[0]
                    h = 1e-7
                    df = (zeta_fib(np.array([z + h]), K=120)[0] - zeta_fib(np.array([z - h]), K=120)[0]) / (2 * h)
                    z = z - f / df
                zs.append({"s": [z.real, z.imag], "residuo": float(abs(zeta_fib(np.array([z]), K=120)[0])), "celula": nz})
    zs.sort(key=lambda r: r["s"][1])
    np_dentro = sum(1 for p in polos if dentro(p, S0, S1, T0, T1))
    total = _winding(S0, S1, T0, T1, n=20000)
    return {"retangulo": [S0, S1, T0, T1], "argumento_zeros_menos_polos": total, "polos_no_retangulo": np_dentro,
            "zeros": zs, "n": len(zs), "zeta_fib_2_serie": float(np.real(zeta_fib(np.array([2.0 + 0j]))[0])),
            "zeta_fib_2_direto": direto, "re_dos_zeros": sorted(round(r["s"][0], 4) for r in zs),
            "espacamento_dos_polos_2pi_sobre_log_phi": 2 * math.pi / LPHI}


def entrada():
    N = 100000
    crivo = bytearray([1]) * (N + 1)
    crivo[0:2] = b"\x00\x00"
    for i in range(2, int(N ** 0.5) + 1):
        if crivo[i]:
            crivo[i * i::i] = bytearray(len(crivo[i * i::i]))
    primos = [p for p in range(2, N + 1) if crivo[p]]
    ok, maximal, tot = 0, 0, 0
    for p in primos:
        r = p % 5
        e = p if r == 0 else (p - 1 if r in (1, 4) else p + 1)
        a, b = 0, 1
        # F_e mod p por duplicação
        def fibmod(n):
            if n == 0:
                return (0, 1)
            x, y = fibmod(n >> 1)
            c = x * ((2 * y - x) % p) % p
            d = (x * x + y * y) % p
            return (d, (c + d) % p) if n & 1 else (c, d)
        if fibmod(e)[0] == 0:
            ok += 1
        # ordem de entrada z(p): menor n com p | F_n (só para p ≤ 2000)
        if p <= 2000:
            tot += 1
            a, b, n = 0, 1, 0
            while True:
                a, b, n = b, (a + b) % p, n + 1
                if a == 0:
                    break
            maximal += (n == e)
    return {"primos_ate": N, "primos": len(primos), "p_divide_F_p_menos_simbolo": ok,
            "ate_2000": tot, "entrada_maxima_ate_2000": maximal}


def hurwitz_phi():
    from decimal import Decimal, getcontext
    getcontext().prec = 80
    phi = (1 + Decimal(5).sqrt()) / 2
    F = [0, 1]
    while len(F) < 70:
        F.append(F[-1] + F[-2])
    lin = []
    for n in range(2, 61):
        err = abs(phi - Decimal(F[n + 1]) / Decimal(F[n]))
        lin.append({"n": n, "F_n": F[n], "convergente": f"{F[n + 1]}/{F[n]}",
                    "Fn2_vezes_erro": float(Decimal(F[n]) ** 2 * err)})
    return {"tabela": lin, "um_sobre_raiz5": 1 / math.sqrt(5)}


def main():
    out = {"phi": PHI, "log_phi": LPHI, "quartetos": quartetos(), "L1_chi5": L1_chi5(), "zeros_L_chi5": zeros_L(),
           "zeta_fibonacci": zeros_fib(), "entrada": entrada(), "hurwitz": hurwitz_phi()}
    json.dump(out, open("aurea.json", "w"), indent=1, ensure_ascii=False)
    q = out["quartetos"]
    print("teste φ:", q["teste_phi"])
    for nome in ("Epstein m²+5n²", "Davenport–Heilbronn"):
        for x in q[nome]["quartetos"]:
            print(f"  {nome[:4]} b={x['b']:.4f} γ={x['gama']:.3f} γ/b={x['razao_gama_b']:.1f} "
                  f"θ/π={x['angulo_diagonal_sobre_pi']:.6f} falta={x['falta_para_meio']:.2e} |w|={x['li']['abs_w_rho']:.6f}"
                  f" |w'|={x['li']['abs_w_1_menos_rho_barra']:.6f} prod={x['li']['produto']:.9f}")
    print("L(1,χ5):", out["L1_chi5"])
    zl = out["zeros_L_chi5"]
    print("zeros L(s,χ5) na reta:", [round(z, 6) for z in zl["zeros_na_reta"][:8]], "n(1..T)", zl["n_na_reta_1_a_T"],
          "argumento", round(zl["argumento_conta"], 4))
    zf = out["zeta_fibonacci"]
    print("ζ_F(2):", zf["zeta_fib_2_serie"], zf["zeta_fib_2_direto"], "zeros:", zf["n"], "Re:", zf["re_dos_zeros"],
          "polos a cada", zf["espacamento_dos_polos_2pi_sobre_log_phi"])
    print("zeros ζ_F:", [[round(r["s"][0], 4), round(r["s"][1], 4), r["residuo"]] for r in zf["zeros"]])
    print("argumento ζ_F (zeros − polos):", round(zf["argumento_zeros_menos_polos"], 4), "polos:", zf["polos_no_retangulo"])
    print("entrada:", out["entrada"])
    print("Hurwitz:", [round(r["Fn2_vezes_erro"], 8) for r in out["hurwitz"]["tabela"][-5:]], out["hurwitz"]["um_sobre_raiz5"])


if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1 and sys.argv[1] == "fib":   # refaz só a zeta de Fibonacci, guardando o resto
        out = json.load(open("aurea.json"))
        out["zeta_fibonacci"] = zeros_fib()
        out["hurwitz"] = hurwitz_phi()
        json.dump(out, open("aurea.json", "w"), indent=1, ensure_ascii=False)
        zf = out["zeta_fibonacci"]
        print(zf["n"], zf["re_dos_zeros"], round(zf["argumento_zeros_menos_polos"], 4), zf["polos_no_retangulo"])
        print([[round(r["s"][0], 4), round(r["s"][1], 4), r["residuo"]] for r in zf["zeros"]])
    else:
        main()
