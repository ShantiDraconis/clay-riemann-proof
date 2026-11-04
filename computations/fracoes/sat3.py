"""P vs NP no cotidiano: a transição de fase do 3-SAT aleatório (o "ponto de quebra" em fração α = cláusulas/variáveis).

    python3 sat3.py N R > sat3_nN.json      (N variáveis, R fórmulas por α; padrão 50 e 200)

α de 3 a 6 em passos de 1/4 (semente fixa). DPLL simples (propagação de
unitárias, escolha da variável mais frequente), contando as decisões. Mede a fração de fórmulas satisfatíveis e o
esforço mediano: a fração cai de 1 para 0 perto de α ≈ 4,27 (previsão da física estatística, Mézard–Parisi–Zecchina
2002; provada para k grande por Ding–Sly–Sun 2015), e o esforço tem pico ali. O primeiro momento dá α_c ≤ 5,19
(Fracoes.primeiro_momento_3sat no kernel). Isto é o fenômeno, não P vs NP: o DPLL é exponencial no pior caso.
"""
import json
import random
import sys

sys.setrecursionlimit(10000)


def gera(n, m, rng):
    return [[v if rng.random() < 0.5 else -v for v in rng.sample(range(1, n + 1), 3)] for _ in range(m)]


def dpll(clausulas, n):
    passos = [0]

    def simplifica(cl, lit):
        out = []
        for c in cl:
            if lit in c:
                continue
            if -lit in c:
                c = [x for x in c if x != -lit]
                if not c:
                    return None
            out.append(c)
        return out

    def resolve(cl):
        while True:
            unit = next((c[0] for c in cl if len(c) == 1), None)
            if unit is None:
                break
            cl = simplifica(cl, unit)
            if cl is None:
                return False
        if not cl:
            return True
        cont = {}
        for c in cl:
            for x in c:
                cont[x] = cont.get(x, 0) + 1
        lit = max(cont, key=cont.get)
        passos[0] += 1
        for l in (lit, -lit):
            nc = simplifica(cl, l)
            if nc is not None and resolve(nc):
                return True
        return False

    sat = resolve(clausulas)
    return sat, passos[0]


rng = random.Random(2026)
n = int(sys.argv[1]) if len(sys.argv) > 1 else 50
R = int(sys.argv[2]) if len(sys.argv) > 2 else 200
saida = []
for j in range(13):
    alfa = 3 + j / 4
    m = round(alfa * n)
    sats, ps = 0, []
    for _ in range(R):
        s, p = dpll(gera(n, m, rng), n)
        sats += s
        ps.append(p)
    ps.sort()
    saida.append({"alfa": alfa, "clausulas": m, "fracao_satisfativel": sats / R, "satisfativeis": sats,
                  "decisoes_mediana": ps[R // 2], "decisoes_p90": ps[int(0.9 * R)]})
    print(saida[-1], file=sys.stderr, flush=True)
print(json.dumps({"n": n, "formulas_por_alfa": R, "pontos": saida}, ensure_ascii=False))
