"""Segunda passada: a lombada de cada par fora da reta, lida no vão entre os dois zeros da reta que o cercam.

    python3 lombadas.py > lombadas.json

Para cada zero fora da reta ρ = ½ + b + iγ₀ de Davenport–Heilbronn (até 170) e de Epstein m² + 5n² (até 100; inclui
o zero 0,81117… + 58,50773…i, que a malha de analogos_fora.py pulou e a contagem na reta denunciou):
* o vão (t_a, t_b) da reta que contém γ₀ e o seu tamanho em espaçamentos médios (θ'(γ₀)/π por unidade);
* dentro do vão, o mínimo local de |Z| mais perto de γ₀ (Z' = 0 com Z·Z'' > 0), e b_lombada = √(2|Z|/|Z''|), o b
  que a forma local K((t − t₀)² + b²) dá (Parametro.b_da_lombada);
* κ = −b², o tempo de volta à reta 2b² (Parametro.quarteto_satura_de_bruijn) e κ em unidades de espaçamento²;
* a contagem: S = N_reta + 2k − θ/π − c (c = 0 para DH, sem polo; c = 1 para Epstein, polo em s = 1), que tem que
  oscilar em torno de 0 se a lista dos k pares estiver completa.
"""
import json
import sys

sys.path.insert(0, "/home/claude/ext/mpmath")
from mpmath import mp, mpf, mpc, sqrt, dirichlet, zeta, loggamma, log, pi, exp, findroot, diff

mp.dps = 20
kap = (sqrt(10 - 2 * sqrt(5)) - 2) / (sqrt(5) - 1)
CHI5, CHI5B = [0, 1, 1j, -1j, -1], [0, 1, -1j, 1j, -1]
CHI_4, LEG5 = [0, 1, 0, -1], [0, 1, -1, -1, 1]
CHI_20 = [CHI_4[n % 4] * LEG5[n % 5] for n in range(20)]
FUN = {
    "dh": (lambda s: (1 - 1j * kap) / 2 * dirichlet(s, CHI5) + (1 + 1j * kap) / 2 * dirichlet(s, CHI5B),
           lambda t: t / 2 * log(5 / pi) + loggamma(mpf(3) / 4 + 1j * t / 2).imag, 0, "Davenport–Heilbronn"),
    "epstein": (lambda s: zeta(s) * dirichlet(s, CHI_20) + dirichlet(s, CHI_4) * dirichlet(s, LEG5),
                lambda t: t * log(sqrt(20) / (2 * pi)) + loggamma(mpf(1) / 2 + 1j * t).imag, 1, "Epstein m²+5n²"),
}
EXTRA = {"epstein": [{"re": 0.81117208120602838, "im": 58.50773732773190, "b": 0.31117208120602838}]}

saida = {}
for nome, (f, theta, c, chave) in FUN.items():
    z0 = exp(1j * theta(mpf("10.3"))) * f(mpc(0.5, mpf("10.3")))
    fase = z0 / abs(z0)
    Z = lambda t: (exp(1j * theta(t)) * f(mpc(0.5, t)) / fase).real
    dados = json.load(open(f"{nome}.json"))
    zeros = sorted(dados["zeros"])
    # zeros da reta em (0, 1]: a primeira passada começou em t = 1
    baixos = []
    ts = [0.005 * j for j in range(1, 201)]
    vs = [float(Z(mpf(t))) for t in ts]
    for (a, va), (b_, vb) in zip(zip(ts, vs), zip(ts[1:], vs[1:])):
        if va * vb < 0:
            baixos.append(float(findroot(Z, (mpf(a), mpf(b_)), solver="anderson")))
    zeros = sorted(baixos + zeros)
    fora = json.load(open("../aglomeracoes/analogos_fora.json"))[chave]["zeros"] + EXTRA.get(nome, [])
    fora = sorted(fora, key=lambda z: z["im"])
    linhas = []
    for z in fora:
        g0, b = z["im"], z["b"]
        ta = max(x for x in zeros if x < g0)
        tb = min(x for x in zeros if x > g0)
        dens = float(diff(theta, g0) / pi)
        # extremos de Z no vão: zeros de Z' numa malha fina
        h = (tb - ta) / 400
        grade = [ta + h * j for j in range(1, 400)]
        dz = [float(diff(Z, mpf(t))) for t in grade]
        cands = []
        for (a, da), (b_, db) in zip(zip(grade, dz), zip(grade[1:], dz[1:])):
            if da * db < 0:
                tm = float(findroot(lambda x: diff(Z, x), (mpf(a), mpf(b_)), solver="anderson"))
                zm = float(Z(mpf(tm)))
                z2 = float(diff(Z, mpf(tm), 2))
                if zm * z2 > 0:          # mínimo local de |Z|
                    cands.append((abs(tm - g0), tm, zm, z2))
        if cands:
            _, tm, zm, z2 = min(cands)
            bl = (2 * abs(zm) / abs(z2)) ** 0.5
        else:
            tm = zm = z2 = bl = None
        linhas.append({"rho": [z["re"], g0], "b": b, "kappa": -b * b, "tempo_de_volta_2b2": 2 * b * b,
                       "kappa_em_espacamentos2": -(b * dens) ** 2, "vao_na_reta": [ta, tb],
                       "vao_em_espacamentos_medios": (tb - ta) * dens, "minimo_de_abs_Z_no_vao": cands != [],
                       "t_lombada": tm, "Z_lombada": zm, "Z_seg": z2, "b_lombada": bl,
                       "erro_relativo": (bl - b) / b if bl else None,
                       "dist_lombada_gama0": (tm - g0) if tm else None})
    serie = []
    for T in [0.5 * j for j in range(2, 2 * int(dados["ate"]) + 1)]:
        nr = sum(1 for x in zeros if x <= T)
        k = sum(1 for z in fora if z["im"] <= T)
        serie.append({"T": T, "N_reta": nr, "pares_fora": k, "S_reta": nr - float(theta(mpf(T)) / pi) - c,
                      "S": nr + 2 * k - float(theta(mpf(T)) / pi) - c})
    Ss = [r["S"] for r in serie]
    saida[nome] = {"funcao": chave, "ate": dados["ate"], "constante_c": c, "zeros_na_reta": len(zeros),
                   "zeros_na_reta_abaixo_de_1": baixos, "pares_fora": len(fora),
                   "N_total_ate_o_topo": len(zeros) + 2 * len(fora),
                   "S_media": sum(Ss) / len(Ss), "S_min": min(Ss), "S_max": max(Ss),
                   "fora": linhas, "serie": serie}
    print(nome, "ok", file=sys.stderr, flush=True)
print(json.dumps(saida, ensure_ascii=False))
