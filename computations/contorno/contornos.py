"""O primeiro zero medido no círculo e no quadrado: as medidas do certificado levadas aos dois contornos.

    python3 contornos.py        (grava contornos.json; ~1 min)

Centro z₀ = ½ + 14,1347251417 i (o de `CertifiedZeros/FirstZero.lean`). Contornos:
  círculo  C_ρ = {|s − z₀| = ρ}               (bola euclidiana; é a que o kernel usa em `cota_grosseira`)
  quadrado Q_a = {max(|Re(s − z₀)|, |Im(s − z₀)|) = a}   (bola ℓ∞; é a forma dos retângulos `ret` do kernel)
Pelo princípio do máximo, max |ζ| no disco (no quadrado cheio) é o máximo no bordo.

Medidas transferidas para cada contorno:
  B      cota de |ζ| no disco/quadrado: 240 (ATK, Euler–Maclaurin de ordem 1), `cotaQ` (a cota grosseira geral do
         kernel, `CrudeBound.cotaQ`, melhor N, M), e o máximo medido no contorno;
  F₁, F₂ Cauchy encaixado (o que o kernel tem: `norm_deriv_le_of_forall_mem_sphere_norm_le` duas vezes), raios
         r₁ = r₂ = (ρ − R)/2: F₂ = B/(r₁r₂); e Cauchy direto no contorno, para comparar;
  R      raio da bola de unicidade (contração g(z) = z − ζ(z)/c, constante ½): F₂·R ≤ |c|/2 − (folga);
  h(d)   passo da malha de retângulos sem zeros a distância d de ρ₁: |ζ(centro)| ≥ F₁·h;
  n      número de retângulos (quadtree) para cobrir {Re ≥ ½} ∩ {R ≤ |s − z₀| ≤ 0,2};
  custo  número de avaliações certificadas para certificar a própria cota B no contorno.
Nada aqui é certificado: é ponto flutuante (Euler–Maclaurin, N = 30, M = 12, erro < 10⁻¹³).
"""
import json
import math
from fractions import Fraction as Fr

import numpy as np

from zeta_em import deriv, zeta

T0 = 14.1347251417
Z0 = complex(0.5, T0)
RAIOS = [0.05, 0.1, 0.15, 0.2, 0.25, 0.3, 0.35, 0.4]


# ---------------------------------------------------------------- o zero e as derivadas
def newton(z, it=8):
    for _ in range(it):
        z = z - zeta(z) / deriv(zeta, z, 1, r=0.01)
    return z


RHO1 = newton(Z0)
D1 = deriv(zeta, RHO1, 1, r=0.01)
D2 = deriv(zeta, RHO1, 2, r=0.05)
D3 = deriv(zeta, RHO1, 3, r=0.05)
C = complex(0.783297, 0.124696)          # cQ do certificado (cQ.1, cQ.2), ≈ ζ′(z₀)


# ---------------------------------------------------------------- máximos nos contornos
def circulo(rho, m=16384):
    th = 2 * np.pi * np.arange(m) / m
    return Z0 + rho * np.exp(1j * th)


def quadrado(a, m=4096):
    u = -a + 2 * a * np.arange(m) / m
    return np.concatenate([Z0 + a + 1j * u, Z0 - u + 1j * a, Z0 - a - 1j * u, Z0 + u - 1j * a])


def maximo(pts):
    v = np.abs(zeta(pts))
    k = int(np.argmax(v))
    return float(v[k]), complex(pts[k])


# ---------------------------------------------------------------- cotaQ (CrudeBound.cotaQ, em Fraction)
BTAB = {0: Fr(1), 1: Fr(-1, 2), 2: Fr(1, 6), 4: Fr(-1, 30), 6: Fr(1, 42), 8: Fr(-1, 30), 10: Fr(5, 66)}


def poch(R, k):
    p = Fr(1)
    for i in range(k):
        p *= R + i
    return p


def cotaQ(N, M, R, d):
    soma = sum(abs(BTAB.get(j, 0)) / math.factorial(j) * poch(R, j - 1) / Fr(N) ** (j - 1) for j in range(2, M + 1))
    cb = sum(abs(BTAB.get(i, 0)) * math.comb(M, i) for i in range(M + 1))
    return N + Fr(N) / d + Fr(1, 2) + soma + poch(R, M) / math.factorial(M) * (cb / Fr(N) ** (M - 1) / (M - 1))


def melhor_cotaQ(R, d):
    R, d = Fr(R).limit_denominator(1000), Fr(d).limit_denominator(1000)
    best = None
    for N in range(1, 80):
        for M in range(2, 11):
            v = cotaQ(N, M, R, d)
            if best is None or v < best[0]:
                best = (v, N, M)
    return float(best[0]), best[1], best[2]


def regiao(forma, rho):
    """R ≥ max‖w‖ e d ≤ min‖w − 1‖ na região (disco ou quadrado cheio de raio rho em volta de z₀)."""
    if forma == "circulo":
        return abs(Z0) + rho, abs(Z0 - 1) - rho
    cant = complex(0.5 + rho, T0 + rho)
    return abs(cant), math.hypot(max(0.0, 1 - (0.5 + rho)), T0 - rho)


# ---------------------------------------------------------------- raio de unicidade
def raio_unicidade(F2_de_R, folga=0.0):
    """Maior R com F₂(R)·R ≤ Re c/2 − folga (o certificado do kernel usa Re c = cQ.1)."""
    alvo = C.real / 2 - folga
    lo, hi = 0.0, 0.5
    for _ in range(200):
        mid = (lo + hi) / 2
        f2 = F2_de_R(mid)
        if f2 is not None and f2 * mid <= alvo:
            lo = mid
        else:
            hi = mid
    return lo


def raio_ideal():
    """Maior R com sup_{|z − z₀| ≤ R} |ζ′(z) − c| ≤ |c|/2 (princípio do máximo: basta o bordo)."""
    lo, hi = 0.0, 3.0
    th = 2 * np.pi * np.arange(256) / 256
    for _ in range(50):
        mid = (lo + hi) / 2
        pts = Z0 + mid * np.exp(1j * th)
        d1 = np.array([deriv(zeta, p, 1, r=0.01) for p in pts])
        if np.max(np.abs(d1 - C)) <= abs(C) / 2:
            lo = mid
        else:
            hi = mid
    return lo


# ---------------------------------------------------------------- cobertura sem zeros (quadtree)
def cobertura(F1, R, D=0.2, max_folhas=3_000_000):
    """Quadrados que cobrem {Re ≥ ½, R ≤ |s − z₀| ≤ D} com |ζ(centro)| ≥ F₁·(meia diagonal)."""
    lado0 = D / 8
    cs = [complex(0.5 + lado0 * (i + 0.5), T0 - D + lado0 * (j + 0.5)) for i in range(8) for j in range(16)]
    cs, lado = np.array(cs), lado0
    folhas, nivel, hmin = 0, 0, None
    while len(cs):
        h = lado / math.sqrt(2)
        dist = np.abs(cs - Z0)
        fora = dist - h > D                       # inteiro fora do anel externo: não precisa
        dentro = dist + h <= R                    # inteiro dentro da bola de unicidade
        cs = cs[~fora & ~dentro]
        if not len(cs):
            break
        ok = np.abs(zeta(cs)) >= F1 * h
        folhas += int(ok.sum())
        if ok.any():
            hmin = h
        cs = cs[~ok]
        if folhas + 4 * len(cs) > max_folhas:
            return None, None, nivel
        q = lado / 4
        cs = np.concatenate([cs + q + 1j * q, cs + q - 1j * q, cs - q + 1j * q, cs - q - 1j * q])
        lado /= 2
        nivel += 1
    return folhas, hmin, nivel


def cobertura_formula(F1, R, D=0.2):
    """Estimativa: anel |ζ| ≈ |ζ′(ρ₁)|d, h = |ζ′|d/F₁, quadrados de lado √2 h: n ≈ (π F₁²/(2|ζ′|²)) ln(D/R)."""
    return math.pi * F1 ** 2 / (2 * abs(D1) ** 2) * math.log(D / R)


# ---------------------------------------------------------------- custo de certificar a cota no contorno
def custo_contorno(forma, rho, Mmed, Bcrude_fn):
    """Centros espaçados s no contorno; Lipschitz de ζ perto do contorno L = B_grosseira(ρ + r_c)/r_c com
    r_c < Re mínimo da região (cota_geral pede Re w > 0). Alvo: B = 1,25·M (folga de 25%).
    s = 2(B − M)/L; avaliações = perímetro/s. Escolhe o melhor r_c."""
    alvo = 1.25 * Mmed
    per = 2 * math.pi * rho if forma == "circulo" else 8 * rho
    remin = 0.5 - rho
    melhor = None
    for frac in np.linspace(0.05, 0.95, 37):
        rc = frac * remin
        bc = Bcrude_fn(forma, rho + rc)
        L = bc / rc
        s = 2 * (alvo - Mmed) / L
        n = math.ceil(per / s)
        if melhor is None or n < melhor["avaliacoes"]:
            melhor = {"r_c": rc, "B_grosseira_vizinhanca": bc, "L": L, "espacamento": s, "avaliacoes": n,
                      "B_alvo": alvo}
    return melhor


def main():
    out = {"z0": [Z0.real, Z0.imag], "rho1": [RHO1.real, RHO1.imag], "dist_z0_rho1": abs(Z0 - RHO1),
           "zeta1": [D1.real, D1.imag], "abs_zeta1": abs(D1), "zeta2": [D2.real, D2.imag], "abs_zeta2": abs(D2),
           "zeta3": [D3.real, D3.imag], "abs_zeta3": abs(D3), "c": [C.real, C.imag]}
    # distâncias de ρ₁
    rho2 = newton(complex(0.5, 21.022039638771555))
    out["distancias"] = {
        "polo_s_igual_1": abs(RHO1 - 1), "rho2": abs(RHO1 - rho2), "conjugado": 2 * RHO1.imag,
        "altura_13": RHO1.imag - 13, "borda_Re_0": 0.5, "z0": abs(Z0 - RHO1), "bola_kernel": 1e-6,
        "trivial_menos_2": abs(RHO1 + 2), "rho2_valor": [rho2.real, rho2.imag]}

    crude_cache = {}

    def bcrude(forma, rho):
        key = (forma, round(rho, 6))
        if key not in crude_cache:
            R, d = regiao(forma, rho)
            crude_cache[key] = melhor_cotaQ(R, d)[0]
        return crude_cache[key]

    tab = []
    for forma, pts_fn in (("circulo", circulo), ("quadrado", quadrado)):
        for rho in RAIOS:
            M, arg = maximo(pts_fn(rho))
            R, d = regiao(forma, rho)
            bq, Nq, Mq = melhor_cotaQ(R, d)
            B = 1.25 * M
            R_enc = raio_unicidade(lambda R, B=B, rho=rho: 4 * B / (rho - R) ** 2 if R < rho else None, folga=0.003)
            linha = {"forma": forma, "raio": rho, "perimetro": 2 * math.pi * rho if forma == "circulo" else 8 * rho,
                     "B_25": B, "R_encaixado_25": R_enc,
                     "max_medido": M, "onde": [arg.real - 0.5, arg.imag - T0], "cotaQ": bq, "cotaQ_N": Nq,
                     "cotaQ_M": Mq, "custo": custo_contorno(forma, rho, M, bcrude)}
            tab.append(linha)
    out["contornos"] = tab

    # transferência das medidas: B → F₂ → R → cobertura
    def m(forma, rho):
        return next(x for x in tab if x["forma"] == forma and x["raio"] == rho)

    rho = 0.4
    fontes = [("ATK 240 (ordem 1)", 240.0, "circulo"),
              ("cotaQ no disco", m("circulo", rho)["cotaQ"], "circulo"),
              ("cotaQ no quadrado", m("quadrado", rho)["cotaQ"], "quadrado"),
              ("quadrado medido +25%", 1.25 * m("quadrado", rho)["max_medido"], "quadrado"),
              ("círculo medido +25%", 1.25 * m("circulo", rho)["max_medido"], "circulo"),
              ("círculo medido exato", m("circulo", rho)["max_medido"], "circulo")]
    trans = []
    for nome, B, forma in fontes:
        encaixado = lambda R, B=B: 4 * B / (rho - R) ** 2 if R < rho else None
        if forma == "circulo":
            direto = lambda R, B=B: 2 * B * rho / (rho - R) ** 3 if R < rho else None
        else:
            direto = lambda R, B=B: 8 * rho * B / (math.pi * (rho - R) ** 3) if R < rho else None
        R_enc = raio_unicidade(encaixado, folga=0.003)
        R_dir = raio_unicidade(direto, folga=0.003)
        F1 = B / (rho - 0.2)                      # Lipschitz de ζ em |s − z₀| ≤ 0,2 (esfera de raio ρ − 0,2)
        n, hmin, niv = cobertura(F1, R_enc) if F1 < 80 else (None, None, None)
        trans.append({"fonte": nome, "B": B, "contorno": forma, "F2_em_R0_encaixado": 4 * B / rho ** 2,
                      "F2_em_R0_direto": direto(0.0), "R_encaixado": R_enc, "R_direto": R_dir,
                      "F1_anel": F1, "h_em_d_1e-3": abs(D1) * 1e-3 / F1,
                      "cobertura_simulada": n, "h_minimo": hmin, "niveis": niv,
                      "cobertura_formula": cobertura_formula(F1, R_enc)})
    out["transferencia"] = trans
    out["R_ideal"] = raio_ideal()
    # o mesmo em ATK: F₂ = 240/0,19², bola 10⁻⁶ (o que está no kernel hoje)
    F2atk = 240 / 0.19 ** 2
    out["kernel_hoje"] = {"F2": F2atk, "R": 1e-6, "R_maximo_com_F2": (C.real / 2 - 0.003) / F2atk,
                          "F1": 240 / 0.19, "h_em_d_1e-6": abs(D1) * 1e-6 / (240 / 0.19),
                          "cobertura_formula": cobertura_formula(240 / 0.19, 1e-6)}
    # o círculo de Li: w = 1 − 1/s leva a reta Re s = ½ no círculo |w| = 1
    w1 = 1 - 1 / RHO1
    ang = lambda t: math.pi - 2 * math.atan(2 * t)
    out["circulo_de_Li"] = {
        "w1": [w1.real, w1.imag], "abs_w1": abs(w1), "angulo_rho1": ang(RHO1.imag), "angulo_13": ang(13.0),
        "arco_entre_13_e_rho1": ang(13.0) - ang(RHO1.imag),
        "raio_imagem_bola_kernel": 1e-6 / abs(RHO1) ** 2,
        "raio_imagem_bola_ideal": out["R_ideal"] / abs(RHO1) ** 2,
        "defeito_por_unidade_de_b": 2 / abs(RHO1) ** 2}
    json.dump(out, open("contornos.json", "w"), indent=1, ensure_ascii=False)
    print(json.dumps({k: out[k] for k in ("rho1", "abs_zeta1", "abs_zeta2", "R_ideal")}, indent=1))
    for x in tab:
        print(f"{x['forma']:9s} {x['raio']:.2f}  max={x['max_medido']:.4f}  cotaQ={x['cotaQ']:.3f} (N={x['cotaQ_N']},M={x['cotaQ_M']})"
              f"  custo={x['custo']['avaliacoes']} (r_c={x['custo']['r_c']:.3f}, L={x['custo']['L']:.1f})  R={x['R_encaixado_25']:.4f}")
    for t in trans:
        print(f"{t['fonte']:24s} B={t['B']:9.3f} F2enc={t['F2_em_R0_encaixado']:9.1f} R_enc={t['R_encaixado']:.3e}"
              f" R_dir={t['R_direto']:.3e} n={t['cobertura_simulada']} (fórmula {t['cobertura_formula']:.3g})")
    print(out["kernel_hoje"], out["circulo_de_Li"], out["distancias"])


if __name__ == "__main__":
    main()
