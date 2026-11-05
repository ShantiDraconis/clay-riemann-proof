"""Oito cópias da estrutura de Riemann giradas de 45° em torno do 0 absoluto: onde caem os zeros.

    python3 oito_copias.py      (grava oito_copias.json; alguns segundos)

Cópia k (k = 0, …, 7): s ↦ ωᵏ s, com ω = e^{iπ/4} = (1 + i)/√2. A cópia 0 é ζ.

- As 8 retas críticas copiadas, ωᵏ·{Re s = ½}, são tangentes ao círculo |s| = ½ (kernel: `copias_da_reta_tangentes`):
  cercam um octógono regular de apótema ½. Duas delas, com Δk = 1, 2, 3, se cruzam a |s| = ½/cos(Δk·π/8); com Δk = 4
  são paralelas, a distância 1 (formam um corredor de largura 1 pelo 0).
- Um zero ρ = ½ + b + iγ vai, na cópia k, para raio |ρ| e ângulo 45°k + arg ρ; fica a arctan((½ + b)/|γ|) < 1/13 rad
  do seu raio (kernel: `zeros_nos_raios`) e a |b| da sua reta crítica.
- Em torno de ½ (comparação): a cópia de 180° é s ↦ 1 − s (kernel: `oito_copias_no_meio`), e o quarteto vira 16
  pontos ½ + ωᵏ(±b ± iγ), em pares a ±δ dos 8 raios, δ = arctan(b/γ); 16-ágono regular só se γ/b = cot(π/16).

Os zeros de ζ até a altura 100 são achados aqui (malha em Re s = ½ + Newton, com `zeta_em`, não certificado), só para
desenhar; nada do que se conclui depende deles. Os quartetos fora da reta de exemplo são os de `aurea.json` (Epstein
m² + 5n² e Davenport–Heilbronn: outras funções com a mesma simetria s ↔ 1 − s; ζ não tem nenhum conhecido).
"""
import json
import math

import numpy as np

from zeta_em import erro_em, zeta

W = complex(math.cos(math.pi / 4), math.sin(math.pi / 4))
S0 = 0.2 + 1j                           # o ponto de teste da conta colada (não é zero: o kernel exclui |Im s| ≤ 13)


def zeros_zeta(t1=100.0):
    t = np.arange(10.0, t1, 0.005)
    a = np.abs(zeta(0.5 + 1j * t))
    i = np.nonzero((a[1:-1] < a[:-2]) & (a[1:-1] < a[2:]) & (a[1:-1] < 0.2))[0] + 1
    out = []
    for z in 0.5 + 1j * t[i]:
        for _ in range(40):
            h = 1e-6
            z = z - zeta(z) / ((zeta(z + h) - zeta(z - h)) / (2 * h))
        if abs(zeta(z)) < 1e-10 and all(abs(z - w) > 1e-6 for w in out):
            out.append(complex(z))
    return sorted(out, key=lambda z: z.imag)


def graus(x):
    return math.degrees(x)


def na_faixa(z):
    return 0 < round(z.real, 12) < 1          # arredonda: ωᵏ·s0 cai às vezes exatamente na borda Re = 1


def cruzamentos():
    """Interseções das retas críticas copiadas: ωʲ{½ + iy} ∩ ωᵏ{½ + iy}; resolve um sistema 2×2 para cada par."""
    linhas = [(W ** k * 0.5, W ** k * 1j) for k in range(8)]        # ponto e direção
    raio = {}
    for j in range(8):
        for k in range(j + 1, 8):
            (p, d), (q, e) = linhas[j], linhas[k]
            M = np.array([[d.real, -e.real], [d.imag, -e.imag]])
            if abs(np.linalg.det(M)) < 1e-12:
                dist = abs(((q - p) * d.conjugate()).imag) / abs(d)
                raio.setdefault("paralelas (Δk = 4): distância", round(dist, 12))
                continue
            u, _ = np.linalg.solve(M, [(q - p).real, (q - p).imag])
            dk = min(k - j, 8 - (k - j))
            raio.setdefault(f"Δk = {dk}", set()).add(round(abs(p + u * d), 9))
    return {k: (sorted(v) if isinstance(v, set) else v) for k, v in raio.items()}


def copias_no_zero(rhos):
    """Para cada zero e cada cópia: ponto, |Re|, e se cai na faixa 0 < Re < 1."""
    linhas = []
    for r in rhos:
        for k in range(8):
            z = W ** k * r
            linhas.append({"k": k, "graus": 45 * k, "s": [z.real, z.imag], "na_faixa": na_faixa(z)})
    return linhas


def quarteto_no_zero(b, g):
    """O quarteto ½ ± b ± iγ nas 8 cópias em torno do 0: 32 pontos em dois anéis (raios |½ ± b + iγ|); em cada anel,
    pares a ±ε dos 8 raios, ε = arctan((½ ± b)/γ). E num braço visto de dentro: desvios ±(½ ± b) do eixo."""
    an = []
    for x in (0.5 + b, 0.5 - b):
        eps = math.atan(x / g)
        an.append({"raio": math.hypot(x, g), "eps_graus": graus(eps), "lacunas_graus": [2 * graus(eps),
                                                                                           45 - 2 * graus(eps)]})
    return {"aneis": an, "desvios_no_braco": sorted([0.5 + b, 0.5 - b, -0.5 + b, -0.5 - b])}


def quarteto_no_meio(b, g):
    d = math.atan(b / g)
    return {"delta_graus": graus(d), "lacunas_16_graus": [2 * graus(d), 45 - 2 * graus(d)],
            "lacunas_8_graus_quatro_copias": [2 * graus(d), 90 - 2 * graus(d)]}


def main():
    zs = zeros_zeta()
    err = max(erro_em(z) for z in zs)
    A = json.load(open("aurea.json"))["quartetos"]
    exemplos = {nome: [{"b": q["b"], "gama": q["gama"], "gama_sobre_b": q["gama"] / q["b"],
                        "no_zero": quarteto_no_zero(q["b"], q["gama"]), "no_meio": quarteto_no_meio(q["b"], q["gama"])}
                       for q in A[nome]["quartetos"]]
                for nome in ("Epstein m²+5n²", "Davenport–Heilbronn")}
    cop = copias_no_zero(zs + [z.conjugate() for z in zs])
    fora = [c for c in cop if c["k"] != 0]
    re_k = {k: min(abs(c["s"][0]) for c in fora if c["k"] == k) for k in range(1, 8)}
    pts = np.array([complex(*c["s"]) for c in cop])
    ks = np.array([c["k"] for c in cop])
    dmin = min(np.min(np.abs(pts[ks != k][:, None] - pts[ks == k][None, :])) for k in range(8))
    t0 = {"no_zero": [], "no_meio": []}
    for k in range(8):
        z = W ** k * S0
        t0["no_zero"].append({"graus": 45 * k, "s": [round(z.real, 6), round(z.imag, 6)], "modulo": abs(z),
                              "angulo_graus": graus(math.atan2(z.imag, z.real)) % 360, "na_faixa": na_faixa(z)})
        z = 0.5 + W ** k * (S0 - 0.5)
        t0["no_meio"].append({"graus": 45 * k, "s": [round(z.real, 6), round(z.imag, 6)], "na_faixa": na_faixa(z)})
    out = {
        "zeros_zeta_ate_100": [[z.real, z.imag] for z in zs], "n_zeros": len(zs), "erro_truncamento_max": err,
        "octogono": {"apotema": 0.5, "raio_vertice": 0.5 / math.cos(math.pi / 8)},
        "cruzamentos_das_retas": cruzamentos(),
        "raio_max_cruzamento": 0.5 / math.cos(3 * math.pi / 8),
        "menor_modulo_de_zero": abs(zs[0]),
        "copias_menor_abs_re_por_k": re_k,
        "copias_k_diferente_de_0_na_faixa": sum(c["na_faixa"] for c in fora),
        "menor_distancia_entre_zeros_de_copias_diferentes": float(dmin),
        "cota_kernel_angulo_ao_raio_rad": 1 / 13, "cota_kernel_angulo_ao_raio_graus": graus(1 / 13),
        "angulo_ao_raio_primeiro_zero_graus": graus(math.atan(0.5 / zs[0].imag)),
        "dezesseis_regular_gama_sobre_b": 1 / math.tan(math.pi / 16),
        "octogono_regular_gama_sobre_b": 1 + math.sqrt(2),
        "anel_regular_exige_gama_menor_que": 1 / math.tan(math.pi / 16),
        "ponto_de_teste_0_2_mais_i": t0,
        "exemplos_fora_da_reta": exemplos,
        "translacoes": {"meia_volta_no_0_depois_1_menos_s": "s ↦ s + 1",
                        "unidades_raiz2_menos_1": [(math.sqrt(2) - 1) ** n for n in range(1, 7)]},
    }
    json.dump(out, open("oito_copias.json", "w"), indent=1, ensure_ascii=False)
    print("zeros de ζ até 100:", len(zs), "| erro de truncamento ≤", f"{err:.1e}")
    print("cruzamentos:", out["cruzamentos_das_retas"])
    print("menor |Re| por cópia k:", {k: round(v, 3) for k, v in re_k.items()},
          "| pontos de cópias k≠0 na faixa:", out["copias_k_diferente_de_0_na_faixa"])
    print("menor distância entre zeros de cópias diferentes:", round(dmin, 4))
    print("ângulo ao raio do 1º zero:", round(out["angulo_ao_raio_primeiro_zero_graus"], 3), "° (cota kernel",
          round(out["cota_kernel_angulo_ao_raio_graus"], 3), "°)")
    for k, v in t0.items():
        print("s0 = 0,2 + i,", k, [(r["graus"], r["s"], r["na_faixa"]) for r in v])
    for nome, xs in exemplos.items():
        q = xs[0]
        print(nome, "1º:", round(q["b"], 4), round(q["gama"], 3), "| no 0:",
              [(round(a["raio"], 4), [round(x, 3) for x in a["lacunas_graus"]]) for a in q["no_zero"]["aneis"]],
              "| no ½:", [round(x, 3) for x in q["no_meio"]["lacunas_16_graus"]])
    print("16-ágono regular em ½: γ/b =", round(out["dezesseis_regular_gama_sobre_b"], 4))


if __name__ == "__main__":
    main()
