"""Confere, valor por valor, os números das duas colagens sobre o "eixo Riemann"."""
import json
import math
import sys
from decimal import Decimal, getcontext

sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else '.')
from zeta_dp import zeta, derivadas, theta, Z  # noqa: E402

G0 = [14.134725141734693790, 21.022039638771554993, 25.010857580145688763, 30.424876125859513210,
      32.935061587739189691, 37.586178158825671257, 40.918719012147495187, 43.327073280914999519,
      48.005150881167159727, 49.773832477672302181]


def refina(g):
    for _ in range(6):
        h = 1e-6
        g -= Z(g) / ((Z(g + h) - Z(g - h)) / (2 * h))
    return g


G = [refina(g) for g in G0]
linhas = []


def c(label, calc, alegado, tol=6e-5):
    calc = complex(calc)
    alegado = complex(alegado)
    erro = abs(calc - alegado)
    rel = erro / max(abs(calc), 1e-300)
    ok = erro <= tol or rel <= 2e-5
    linhas.append({"item": label, "calculado": [round(calc.real, 6), round(calc.imag, 6)],
                   "alegado": [alegado.real, alegado.imag], "erro": erro, "ok": ok})


# A. zeros triviais
triv = {-2: (-0.03044, -0.06576, -0.08321), -4: (0.00798, 0.00573, -0.01077), -6: (-0.00589, 0.00034, 0.01174),
        -8: (0.00831, -0.00501, -0.01529), -10: (-0.01892, 0.01944, 0.02631)}
for s, (d1, d2, d3) in triv.items():
    d = derivadas(s, 3, r=0.25)
    c(f"A ζ'({s})", d[1], d1, 1e-5)
    c(f"A ζ''({s})", d[2], d2, 1e-5)
    c(f"A ζ'''({s})", d[3], d3, 1e-5)
c("A ζ'(-20)", derivadas(-20, 1)[1], 132.28099, 1e-4)
for s, al in {-1.99: -0.000307, -3.99: 0.000080, -5.99: -0.000058, -7.99: 0.000082, -9.99: -0.000188}.items():
    c(f"A ζ({s})", zeta(s), al, 2e-6)

# B. zeros na reta: ζ', ζ'', ζ'''
reta = [((0.78329, 0.12469), (-0.61440, -0.22978), (0.47051, 0.32062)),
        ((1.10929, -0.24872), (-1.31332, 0.41746), (1.62321, -0.50360)),
        ((1.29579, 0.45003), (-1.67329, -0.95761), (2.15081, 1.61416)),
        ((1.12013, -0.66750), (-1.46307, 1.56259), (2.15798, -2.84538)),
        ((1.16057, 0.75055), (-1.52208, -1.86274), (2.13321, 3.63730)),
        ((1.85346, -0.56100), (-3.20335, 1.37350), (5.50389, -2.66890)),
        ((1.45951, -0.30286), (-2.66512, 0.90265), (5.22758, -2.01155)),
        ((1.46408, 1.10372), (-2.17429, -2.99693), (3.30534, 6.50390)),
        ((1.03392, -1.17886), (-1.04252, 3.32668), (0.96497, -7.54715)),
        ((1.26089, 0.65078), (-2.18654, -2.16640), (4.40185, 5.54200))]
for k, (g, ders) in enumerate(zip(G, reta), 1):
    d = derivadas(0.5 + 1j * g, 3, r=0.2)
    for o, (re, im) in enumerate(ders, 1):
        c(f"B ζ^({o}) no zero {k} (t={g:.4f})", d[o], complex(re, im))

# C. fora da reta, tabelas 1–3
tab1 = {0.0: ((-0.47917, -0.09892), (1.15679, 0.28931), (-0.89553, -0.45098)),
        0.2: ((-0.26487, -0.04933), (0.99036, 0.21002), (-0.77148, -0.34616)),
        0.3: ((-0.16959, -0.02999), (0.91604, 0.17763), (-0.71545, -0.30253)),
        0.4: ((-0.08148, -0.01367), (0.84714, 0.14934), (-0.66316, -0.26391)),
        0.45: ((-0.03994, -0.00652), (0.81461, 0.13659), (-0.63835, -0.24632)),
        0.49: ((-0.00786, -0.00125), (0.78946, 0.12701), (-0.61913, -0.23300)),
        0.51: ((0.00780, 0.00123), (0.77717, 0.12241), (-0.60972, -0.22659)),
        0.55: ((0.03840, 0.00595), (0.75315, 0.11360), (-0.59129, -0.21424)),
        0.6: ((0.07533, 0.01137), (0.72415, 0.10326), (-0.56899, -0.19963)),
        0.7: ((0.14497, 0.02074), (0.66939, 0.08465), (-0.52674, -0.17304)),
        0.8: ((0.20934, 0.02838), (0.61870, 0.06854), (-0.48744, -0.14961)),
        1.0: ((0.32382, 0.03937), (0.52843, 0.04266), (-0.41705, -0.11087)),
        2.0: ((0.68918, 0.04752), (0.23994, -0.01127), (-0.18900, -0.01776))}
tab2 = {0.0: ((-0.75874, 0.18838), (2.01950, -0.53131)), 0.2: ((-0.39994, 0.09584), (1.58654, -0.39892)),
        0.3: ((-0.25043, 0.05880), (1.40735, -0.34296)), 0.4: ((-0.11777, 0.02704), (1.24909, -0.29307)),
        0.49: ((-0.01115, 0.00250), (1.12251, -0.25292)), 0.51: ((0.01102, -0.00246), (1.09624, -0.24458)),
        0.6: ((0.10462, -0.02286), (0.98574, -0.20942)), 0.7: ((0.19762, -0.04203), (0.87652, -0.17468)),
        0.8: ((0.28034, -0.05794), (0.77991, -0.14407)), 1.0: ((0.41956, -0.08149), (0.61876, -0.09366)),
        2.0: ((0.79077, -0.10383), (0.20390, 0.02001))}
tab3 = {0.0: ((-0.90999, -0.38613), (2.46849, 1.19560)), 0.2: ((-0.47471, -0.18631), (1.90814, 0.82285)),
        0.4: ((-0.13831, -0.05007), (1.47434, 0.55430)), 0.6: ((0.12156, 0.04047), (1.13877, 0.36193)),
        0.8: ((0.32226, 0.09839), (0.87934, 0.22515)), 1.0: ((0.47722, 0.13322), (0.67887, 0.12883)),
        2.0: ((0.85785, 0.14640), (0.18583, -0.04547))}
for nome, g, tab in (("t=γ1", G[0], tab1), ("t=γ2", G[1], tab2), ("t=γ3", G[2], tab3)):
    for sig, vals in tab.items():
        d = derivadas(sig + 1j * g, len(vals) - 1, r=0.2)
        for o, (re, im) in enumerate(vals):
            c(f"C ζ^({o})({sig}+i·{nome})", d[o], complex(re, im))

# D. t grande
grandes = {(0.6, 100): ((2.36369, -0.03722), (-2.88819, -0.14435)),
           (0.4, 100): ((3.11765, 0.00203), (-4.82177, -0.25659)),
           (0.6, 1000): ((0.62886, 0.59846), (2.03581, -2.70654)),
           (0.4, 1000): ((-0.11489, 1.43672), (6.09840, -6.19153)),
           (0.6, 10000): ((-0.13128, -0.42407), (2.14103, -2.46481)),
           (0.4, 10000): ((-0.45940, 0.80619), (0.13030, -11.94056))}
for (sig, t), vals in grandes.items():
    d = derivadas(sig + 1j * t, 1, r=0.05, M=64)
    c(f"D ζ({sig}+{t}i)", d[0], complex(*vals[0]))
    c(f"D ζ'({sig}+{t}i)", d[1], complex(*vals[1]), 2e-4)
for (t, sig), al in {(100, 0.6): 0.329, (100, 0.7): 0.584, (1000, 0.6): 0.430, (1000, 0.7): 0.702,
                     (10000, 0.6): 0.439, (10000, 0.7): 0.683}.items():
    # alegado com 3 casas, truncado: tolerância de 1e-3
    c(f"D |I_ζ| = |ζ({sig}+{t}i) − ζ(½+{t}i)|", abs(zeta(sig + 1j * t) - zeta(0.5 + 1j * t)), al, 1e-3)
for sig, al in {2: 0.690, 10: 0.999, 100: 1.000}.items():
    c(f"D |I_ζ| σ={sig}, t=γ1", abs(zeta(sig + 1j * G[0])), al, 1e-3)
d = derivadas(10 + 1j * G[0], 1)
c("E ζ(10+i·γ1)", d[0], complex(0.99907, 0.00035))
c("E ζ'(10+i·γ1)", d[1], complex(0.00064, -0.00024), 1e-5)

# F. Idem (par de valores) e Dual (derivada)
c("F Idem ζ(0,6 + i(γ1+0,02))", zeta(0.6 + 1j * (G[0] + 0.02)), complex(0.07338, 0.02589))
c("F Idem ζ(0,7 + i(γ2−0,05))", zeta(0.7 + 1j * (G[1] - 0.05)), complex(0.19018, -0.08624))
c("F Dual ζ'(ρ1)·(0,1+0,02i)", derivadas(0.5 + 1j * G[0], 1)[1] * (0.1 + 0.02j), complex(0.07583, 0.02813))
c("F Dual ζ'(ρ2)·(0,2−0,05i)", derivadas(0.5 + 1j * G[1], 1)[1] * (0.2 - 0.05j), complex(0.20942, -0.10521))

# G. eixo R puro: alegado coef(c) = ζ'(0)c + ζ''(0)c²/2; no Idem o exato é ζ(c) − ζ(0)
eixo = {0.1: -0.101926, 0.5: -0.710264, 1: -1.922117, 2: -5.850590, 10: -109.507208, 100: -10123.676133}
eixo_exato = {}
for cc, al in eixo.items():
    exato = None if cc == 1 else (zeta(cc) + 0.5).real
    eixo_exato[cc] = exato
    if exato is None:
        linhas.append({"item": "G coef(ζ(1·R))", "calculado": "polo: ζ(1) não existe", "alegado": [al, 0],
                       "erro": float('inf'), "ok": False})
    else:
        c(f"G coef(ζ({cc}·R)) = ζ({cc}) + ½", exato, al, 1e-4)

# H. passos de 0,01 perto dos zeros
h51 = [(0.00780, 0.00123), (0.01102, -0.00246), (0.01287, 0.00445), (0.01112, -0.00659), (0.01152, 0.00741),
       (0.01837, -0.00554), (0.01446, -0.00298), (0.01453, 0.01088), (0.01028, -0.01162), (0.01250, 0.00640)]
for k, (g, v) in enumerate(zip(G, h51), 1):
    c(f"H ζ(0,51 + i·γ{k})", zeta(0.51 + 1j * g), complex(*v), 2e-5)
ht = [(-0.00121, 0.00784), (0.00255, 0.01107), (-0.00441, 0.01300), (0.00674, 0.01112), (-0.00742, 0.01169)]
for k, (g, v) in enumerate(zip(G, ht), 1):
    c(f"H ζ(½ + i(γ{k}+0,01))", zeta(0.5 + 1j * (g + 0.01)), complex(*v), 2e-5)
# o alegado "1/ζ(s+0,01) ≈ ..." é a 1ª ordem 1/(0,01·ζ'(ρ)); o valor exato fica no JSON
for k, al in ((0, (124.50996, -19.82183)), (1, (85.83200, 19.24552))):
    d1 = derivadas(0.5 + 1j * G[k], 1)[1]
    c(f"H 1/(0,01·ζ'(ρ{k + 1})) [1ª ordem de 1/ζ(0,51+iγ{k + 1})]", 1 / (0.01 * d1), complex(*al), 1e-3)
    linhas.append({"item": f"H 1/ζ(0,51+iγ{k + 1}) exato", "calculado": str(1 / zeta(0.51 + 1j * G[k])),
                   "alegado": "-", "erro": 0, "ok": True})
c("H 1/ζ'(ρ1)", 1 / derivadas(0.5 + 1j * G[0], 1)[1], complex(1.24509, -0.19821))
c("H 1/ζ'(ρ2)", 1 / derivadas(0.5 + 1j * G[1], 1)[1], complex(0.85832, 0.19245))

# I. Newton −ζ/ζ'
for (sig, g, al) in ((0.6, G[0], (-0.10415, -0.00085)), (0.7, G[1], (-0.22604, 0.00290)),
                     (2.0, G[0], (-2.85661, -0.33233))):
    d = derivadas(sig + 1j * g, 1)
    c(f"I −ζ/ζ' em {sig}+i·{g:.2f}", -d[0] / d[1], complex(*al))

# J. Taylor de 1ª ordem e erro
for (sig, g, tay, err) in ((0.6, G[0], (0.07832, 0.01246), 0.00319), (0.7, G[1], (0.22185, -0.04974), 0.02542)):
    d1 = derivadas(0.5 + 1j * g, 1)[1]
    c(f"J Taylor (σ−½)ζ'(ρ) em σ={sig}", (sig - 0.5) * d1, complex(*tay))
    c(f"J erro do Taylor em σ={sig}", abs(zeta(sig + 1j * g) - (sig - 0.5) * d1), err, 2e-5)

# K. N(T) para T ≤ 200
contagem = {50: (8.422914, 0.577086, 10), 100: (28.002410, -0.002410, 29), 150: (51.745826, -0.745826, 52),
            200: (78.193280, -0.193280, 79)}
passo = 0.01
ts = [10 + passo * k for k in range(int(190 / passo) + 1)]
zs = [Z(t) for t in ts]
for T, (tp, S, N) in contagem.items():
    trocas = sum(1 for a, b, t in zip(zs, zs[1:], ts[1:]) if a * b < 0 and t <= T)
    c(f"K θ({T})/π", theta(T) / math.pi, tp, 1e-5)
    c(f"K S({T}) = N − θ/π − 1", N - theta(T) / math.pi - 1, S, 1e-5)
    c(f"K trocas de sinal de Z em (10,{T}]", trocas, N, 0)

# L. zero real de ζ' entre −3 e −2,5
a, b = -3.0, -2.5
fa = derivadas(a, 1)[1].real
for _ in range(50):
    m = (a + b) / 2
    fm = derivadas(m, 1)[1].real
    if fa * fm <= 0:
        b = m
    else:
        a, fa = m, fm
c("L zero real de ζ'", (a + b) / 2, -2.717, 5e-4)

# M. alturas gigantes: N(T) ≈ θ(T)/π + 1 (|S(T)| pequeno)
getcontext().prec = 50
PI = Decimal("3.14159265358979323846264338327950288419716939937510")


def theta_d(T):
    T = Decimal(T)
    return T / 2 * (T / (2 * PI)).ln() - T / 2 - PI / 8 + 1 / (48 * T)


alturas = {"3000175332800": 12363153437138, "3000204982471.5": 12363280336724, "3000206422471.5": 12363286499876}
for T, N in alturas.items():
    S = Decimal(N) - theta_d(T) / PI - 1
    linhas.append({"item": f"M S({T}) = N_alegado − θ/π − 1", "calculado": float(S), "alegado": "|S| < 3",
                   "erro": abs(float(S)), "ok": abs(S) < 3})

ruins = [l for l in linhas if not l["ok"]]
print(f"{len(linhas)} valores conferidos, {len(linhas) - len(ruins)} batem, {len(ruins)} não batem\n")
for l in ruins:
    print("NÃO BATE:", l["item"], "calculado", l["calculado"], "alegado", l["alegado"], f"erro {l['erro']:.3g}")
grupos = {}
for l in linhas:
    grupos.setdefault(l["item"][0], []).append(l)
print()
for k, ls in sorted(grupos.items()):
    finitos = [x["erro"] for x in ls if x["ok"]]
    print(k, f"{sum(x['ok'] for x in ls)}/{len(ls)} batem; erro máx. entre os que batem {max(finitos) if finitos else 0:.2g}")
print("\nIdem exato no eixo R (ζ(c) + ½):", {k: (round(v, 6) if v is not None else "polo") for k, v in eixo_exato.items()})
print("zeros refinados:", [round(g, 9) for g in G])
json.dump(linhas, open("resultado_conferencia.json", "w"), ensure_ascii=False, indent=1, default=str)
