"""Resumo da homotopia: para cada par, t_c e C do ajuste b² = C(t − t_c) nos últimos 5 pontos com b > 0,003.

    python3 homotopia_resumo.py > homotopia_resumo.json
"""
import json

d = json.load(open("homotopia_seguir.json"))
saida = []
for z in d["zeros"]:
    pts = [(t, (r - 0.5) ** 2, i) for t, r, i in z["trajetoria"] if abs(r - 0.5) > 0.003][-5:]
    n = len(pts)
    mt = sum(p[0] for p in pts) / n
    mb = sum(p[1] for p in pts) / n
    stt = sum((p[0] - mt) ** 2 for p in pts)
    C = sum((p[0] - mt) * (p[1] - mb) for p in pts) / stt
    tc = mt - mb / C
    res = max(abs(p[1] - C * (p[0] - tc)) for p in pts)
    saida.append({"rho_t1": z["rho_t1"], "b_t1": z["b_t1"], "t_c": tc, "C": C, "gama_no_encontro": pts[-1][2],
                  "residuo_max_do_ajuste": res, "b_em_t_meio": next((abs(r - 0.5) for t, r, _ in z["trajetoria"]
                                                                    if t <= 0.5), None)})
print(json.dumps({"familia": d["familia"], "pares": saida,
                  "fora_da_reta_em_t": {str(t): sum(1 for s in saida if s["t_c"] < t)
                                        for t in (1.0, 0.75, 0.5, 0.25, 0.1, 0.05, 0.02, 0.0)}},
                 ensure_ascii=False, indent=1))
