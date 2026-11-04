"""Onde o padrão se repete fora da reta: Davenport–Heilbronn e Epstein m² + 5n² na reta crítica.

    python3 padrao_fora.py NOME > NOME.json      (NOME = dh ou epstein)

Para f com equação funcional simétrica e coeficientes reais, Z_f(t) = e^{iθ(t)} f(½ + it) é real:
* Epstein m² + 5n² (discriminante −20): Λ(s) = (√20/2π)^s Γ(s) Z(s) = Λ(1 − s), θ(t) = t ln(√20/2π) + Im ln Γ(½ + it);
  Z(s) = ζ(s) L(s, χ₋₂₀) + L(s, χ₋₄) L(s, χ₅).
* Davenport–Heilbronn (χ mod 5 ímpar, χ(2) = i): Λ(s) = (5/π)^{s/2} Γ((s + 1)/2) f(s),
  θ(t) = (t/2) ln(5/π) + Im ln Γ(¾ + it/2).
Saída: os zeros na reta em [1, topo] (trocas de sinal de Z_f, refinadas), S_reta(T) = N_reta(T) − θ(T)/π − c (a
contagem na reta menos a parte suave; c = 0 para DH, que não tem polo, e c = 1 para Epstein, polo em s = 1): cai 2 a
cada par fora da reta, porque a reta não vê o par. Primeira passada da lombada: em cada altura γ₀ de zero fora da
reta já achado (analogos_fora.json), numa janela fixa γ₀ ± 0,6, o ponto de menor |Z_f| e
b_lombada = √(2|Z_min|/|Z''|). A janela fixa às vezes pega um zero da reta vizinho; lombadas.py refaz a leitura dentro
do vão entre os dois zeros da reta que cercam γ₀ (é a que vale).
"""
import json
import sys

sys.path.insert(0, "/home/claude/ext/mpmath")
from mpmath import mp, mpf, mpc, sqrt, dirichlet, zeta, loggamma, log, pi, exp, findroot, diff

mp.dps = 20
NOME = sys.argv[1]
kap = (sqrt(10 - 2 * sqrt(5)) - 2) / (sqrt(5) - 1)
CHI5, CHI5B = [0, 1, 1j, -1j, -1], [0, 1, -1j, 1j, -1]
CHI_4, LEG5 = [0, 1, 0, -1], [0, 1, -1, -1, 1]
CHI_20 = [CHI_4[n % 4] * LEG5[n % 5] for n in range(20)]
if NOME == "dh":
    f = lambda s: (1 - 1j * kap) / 2 * dirichlet(s, CHI5) + (1 + 1j * kap) / 2 * dirichlet(s, CHI5B)
    theta = lambda t: t / 2 * log(5 / pi) + loggamma(mpf(3) / 4 + 1j * t / 2).imag
    TOPO, PASSO, chave, C = 170, 0.02, "Davenport–Heilbronn", 0
else:
    f = lambda s: zeta(s) * dirichlet(s, CHI_20) + dirichlet(s, CHI_4) * dirichlet(s, LEG5)
    theta = lambda t: t * log(sqrt(20) / (2 * pi)) + loggamma(mpf(1) / 2 + 1j * t).imag
    TOPO, PASSO, chave, C = 100, 0.01, "Epstein m²+5n²", 1


def Zc(t):
    return exp(1j * theta(t)) * f(mpc(0.5, t))


# fase global: Z_f(t) = c·(real); acha c em t = 10,3 e confere a realidade em outros pontos
z0 = Zc(mpf("10.3"))
fase = z0 / abs(z0)
Z = lambda t: (Zc(t) / fase)
imag_max = max(abs(Z(mpf(t)).imag) / max(abs(Z(mpf(t))), mpf(10) ** -30) for t in (5.5, 37.1, 77.7, 95.3))
grade = [1 + PASSO * j for j in range(int((TOPO - 1) / PASSO) + 1)]
vals = [float(Z(mpf(t)).real) for t in grade]
zeros = []
for (a, va), (b, vb) in zip(zip(grade, vals), zip(grade[1:], vals[1:])):
    if va == 0 or va * vb < 0:
        try:
            r = findroot(lambda x: Z(x).real, (mpf(a), mpf(b)), solver="anderson")
            zeros.append(float(r))
        except Exception:
            zeros.append((a + b) / 2)
fora = json.load(open("../aglomeracoes/analogos_fora.json"))[chave]["zeros"]
alturas_fora = sorted(z["im"] for z in fora)
# S na reta
serie = []
for T in [1 + 0.5 * j for j in range(int((TOPO - 1) / 0.5) + 1)]:
    n_reta = sum(1 for z in zeros if z <= T)
    serie.append({"T": T, "N_reta": n_reta, "suave": float(theta(mpf(T)) / pi + C),
                  "S_reta": n_reta - float(theta(mpf(T)) / pi) - C,
                  "pares_fora_ate_T": sum(1 for g in alturas_fora if g <= T)})
# em volta de cada zero fora da reta
locais = []
for z in sorted(fora, key=lambda z: z["im"]):
    g0, btrue = z["im"], z["b"]
    antes = [x for x in zeros if x < g0]
    depois = [x for x in zeros if x > g0]
    dens = float(diff(theta, g0) / pi)                          # zeros por unidade de altura (parte suave)
    vazio = (depois[0] - antes[-1]) if antes and depois else None
    # lombada: mínimo de |Z| perto de g0
    ts = [g0 - 0.6 + 0.004 * j for j in range(301)]
    vz = [float(Z(mpf(t)).real) for t in ts]
    k = min(range(len(ts)), key=lambda j: abs(vz[j]))
    tm = ts[k]
    zmin = vz[k]
    z2 = float(diff(lambda x: Z(x).real, mpf(tm), 2))
    troca = any(a * b < 0 for a, b in zip(vz, vz[1:]))
    blomb = (2 * abs(zmin) / abs(z2)) ** 0.5 if z2 != 0 else None
    locais.append({"rho": [z["re"], g0], "b": btrue, "espaco_na_reta": vazio,
                   "espaco_em_espacamentos_medios": vazio * dens if vazio else None,
                   "espacamentos_vizinhos": [(antes[-1] - antes[-2]) * dens, (depois[1] - depois[0]) * dens]
                   if len(antes) > 1 and len(depois) > 1 else None,
                   "Z_troca_de_sinal_perto": troca, "t_do_minimo": tm, "Z_min": zmin, "Z_seg_derivada": z2,
                   "b_da_lombada": blomb})
print(json.dumps({"funcao": chave, "ate": TOPO, "passo": PASSO, "parte_imaginaria_relativa_max": float(imag_max),
                  "zeros_na_reta": len(zeros), "zeros": zeros, "alturas_fora": alturas_fora,
                  "S_reta": serie, "em_volta_dos_fora": locais}, ensure_ascii=False))
