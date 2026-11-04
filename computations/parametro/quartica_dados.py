"""Lacuna L5 nos dados: b lido da lombada com o termo quártico, nos zeros fora da reta de Davenport–Heilbronn e Epstein.

    python3 quartica_dados.py > quartica_dados.json

Perto do mínimo de |Z| no vão, Z ≈ Z_m + (Z''/2)x² + (Z''''/24)x⁴. O par fora da reta é x = ±ib, com b² a raiz
de (Z''''/24)y² − (Z''/2)y + Z_m = 0 mais perto de 0 (y = b²): b²_quártico = (c − √(c² − 4dZ_m))/(2d), c = Z''/2,
d = Z''''/24 (orientado para Z_m > 0). A forma quadrática dá b² = Z_m/c. Compara com o b verdadeiro (Nos.lombada4,
saturacao_superior, saturacao_inferior). mpmath, sem certificação.
"""
import json
import math
import sys

sys.path.insert(0, "/home/claude/ext/mpmath")
from mpmath import mp, mpf, mpc, sqrt, dirichlet, zeta, loggamma, log, pi, exp, diff

mp.dps = 25
kap = (sqrt(10 - 2 * sqrt(5)) - 2) / (sqrt(5) - 1)
CHI5, CHI5B = [0, 1, 1j, -1j, -1], [0, 1, -1j, 1j, -1]
CHI_4, LEG5 = [0, 1, 0, -1], [0, 1, -1, -1, 1]
CHI_20 = [CHI_4[n % 4] * LEG5[n % 5] for n in range(20)]
FUN = {
    "dh": (lambda s: (1 - 1j * kap) / 2 * dirichlet(s, CHI5) + (1 + 1j * kap) / 2 * dirichlet(s, CHI5B),
           lambda t: t / 2 * log(5 / pi) + loggamma(mpf(3) / 4 + 1j * t / 2).imag),
    "epstein": (lambda s: zeta(s) * dirichlet(s, CHI_20) + dirichlet(s, CHI_4) * dirichlet(s, LEG5),
                lambda t: t * log(sqrt(20) / (2 * pi)) + loggamma(mpf(1) / 2 + 1j * t).imag),
}
L = json.load(open("lombadas.json"))
saida = {}
for nome, (f, theta) in FUN.items():
    z0 = exp(1j * theta(mpf("10.3"))) * f(mpc(0.5, mpf("10.3")))
    fase = z0 / abs(z0)
    Z = lambda t: (exp(1j * theta(t)) * f(mpc(0.5, t)) / fase).real
    linhas = []
    for r in L[nome]["fora"]:
        if not r["b_lombada"]:
            linhas.append({"rho": r["rho"], "b": r["b"], "sem_lombada": True})
            continue
        tm = mpf(r["t_lombada"])
        zm = float(Z(tm))
        z2 = float(diff(Z, tm, 2))
        z4 = float(diff(Z, tm, 4))
        sg = 1 if zm > 0 else -1
        zm, c, d = sg * zm, sg * z2 / 2, sg * z4 / 24
        bq2 = zm / c
        disc = c * c - 4 * d * zm
        b4 = None
        if disc >= 0 and d != 0:
            b4 = math.sqrt((c - math.sqrt(disc)) / (2 * d)) if (c - math.sqrt(disc)) / (2 * d) > 0 else None
        linhas.append({"rho": r["rho"], "b": r["b"], "b_quadratico": math.sqrt(bq2), "b_quartico": b4,
                       "erro_quadratico": math.sqrt(bq2) / r["b"] - 1,
                       "erro_quartico": (b4 / r["b"] - 1) if b4 else None, "Z_m": zm, "c": c, "d": d})
    saida[nome] = linhas
print(json.dumps(saida, ensure_ascii=False))
