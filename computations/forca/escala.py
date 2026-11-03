"""Empurrões na escala do próprio Z: quantos zeros saem da reta para cada ε (a partir das lombadas de lombadas.py).

    python3 escala.py LOMBADAS.json SAIDA.json

A função empurrada Z − ε (ε > 0) só perde zeros reais nas lombadas positivas: cada lombada positiva de altura menor
que ε é engolida e os dois zeros que a delimitavam saem da reta como um par ½ ± b + it* (e o quarteto, com a
conjugação); as lombadas negativas ficam mais fundas e seus zeros só se afastam. Z + ε faz o mesmo com as negativas.
Zeros fora da reta = 2 × lombadas engolidas (lombadas de um só pico; as tortas, com dois extremos, são raras e contam
como uma).
"""
import json
import math
import sys

d = json.load(open(sys.argv[1]))
L = d["lombadas"]
n = d["zeros"]
T = 3.0001753e12
rms = math.sqrt(math.log(T / (2 * math.pi)))
pos = sorted(r[2] for r in L if r[2] > 0)
neg = sorted(-r[2] for r in L if r[2] < 0)


def conta(lst, e):
    import bisect
    return bisect.bisect_left(lst, e)


grade = [10 ** (k / 4) for k in range(-20, 8)]
linhas = []
for e in grade:
    cp, cn = conta(pos, e), conta(neg, e)
    linhas.append({"epsilon": e, "epsilon_relativo": e / rms, "Z_menos_eps_fora": 2 * cp,
                   "fracao_Z_menos_eps": 2 * cp / n, "Z_mais_eps_fora": 2 * cn, "fracao_Z_mais_eps": 2 * cn / n})


def quantil(lst, f):
    return lst[min(int(f * len(lst)), len(lst) - 1)]


resumo = {
    "zeros": n, "lombadas_positivas": len(pos), "lombadas_negativas": len(neg), "rms_Z": rms,
    "menor_positiva": pos[0], "menor_negativa": neg[0], "maior_positiva": pos[-1], "maior_negativa": neg[-1],
    "mediana_positiva": quantil(pos, 0.5), "mediana_negativa": quantil(neg, 0.5),
    "epsilon_para_fracao": {f"{f}": [quantil(pos, f), quantil(neg, f)] for f in (0.0001, 0.001, 0.01, 0.1, 0.5, 0.9, 0.99)},
}
out = {"resumo": resumo, "curva": linhas}
json.dump(out, open(sys.argv[2], "w"), ensure_ascii=False, indent=1)
print(json.dumps(resumo, ensure_ascii=False, indent=1))
for l in linhas:
    print(f"ε={l['epsilon']:.2e} ({l['epsilon_relativo']:.1e} rms)  Z−ε: {l['Z_menos_eps_fora']:6d} fora ({100 * l['fracao_Z_menos_eps']:.3f}%)"
          f"   Z+ε: {l['Z_mais_eps_fora']:6d} ({100 * l['fracao_Z_mais_eps']:.3f}%)")
