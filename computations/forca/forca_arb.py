"""A altura da lombada certificada (Arb) nos pares mais frágeis de cada altura.

    python3 forca_arb.py ./forca pontos.json GRUPO SAIDA.json ORCAMENTO_S

Para cada par de pontos.json do GRUPO: Z, Z', Z''/2 no ponto médio m (bolas da Arb), o extremo t* = m − Z'(m)/Z''(m)
(um passo de Newton, que no par apertado já cai a menos de Δ³ do extremo), Z(t*) com Z'' e, para conferir, Z nos dois
zeros (as bolas têm de conter 0). A força mínima de empurrão vertical é |Z(t*)| (README, seção 27).
"""
import json
import re
import subprocess
import sys
import time
from decimal import Decimal, getcontext

getcontext().prec = 60
BIN, PONTOS, GRUPO, SAI, ORC = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], float(sys.argv[5])
INICIO = time.time()


def bola(s):
    m = re.match(r"\[?\s*([0-9.eE+-]+)\s*(?:\+/-\s*([0-9.eE+-]+))?\s*\]?", s)
    return Decimal(m.group(1)), Decimal(m.group(2) or "0")


def Z(t, ln=3, prec=256):
    resto = ORC - (time.time() - INICIO)
    if resto < 60:
        raise TimeoutError("orçamento")
    r = subprocess.run([BIN, str(t), str(ln), str(prec)], capture_output=True, text=True, timeout=resto)
    if r.returncode:
        raise RuntimeError(r.stderr[-300:])
    return [bola(x) for x in json.loads(r.stdout)["Z"]]


out = {"grupo": GRUPO, "pares": []}
for p in [p for p in json.load(open(PONTOS)) if p["grupo"] == GRUPO]:
    reg = dict(p)
    out["pares"].append(reg)
    try:
        g1 = Decimal(p["gamma_1"])
        g2 = Decimal(p["gamma_2"]) if p.get("gamma_2") else g1 + Decimal(p["intervalo"])
        m = (g1 + g2) / 2
        t0 = time.time()
        z0, z1, z2 = Z(m)
        reg["segundos_por_avaliacao"] = round(time.time() - t0, 1)
        ts = m - z1[0] / (2 * z2[0]) if z2[0] != 0 else m
        ze, _, ze2 = Z(ts)
        reg.update({"t_estrela": str(ts), "Z_estrela": f"{ze[0]:.12e} +/- {ze[1]:.3e}",
                    "forca": f"{abs(ze[0]):.12e}", "Zpp": f"{2 * ze2[0]:.12e} +/- {2 * ze2[1]:.3e}",
                    "forca_certificada_entre": [f"{abs(ze[0]) - ze[1]:.12e}", f"{abs(ze[0]) + ze[1]:.12e}"]})
        za = Z(g1, 1)[0]
        zb = Z(g2, 1)[0]
        reg["Z_nos_zeros"] = [f"{za[0]:.3e} +/- {za[1]:.3e}", f"{zb[0]:.3e} +/- {zb[1]:.3e}"]
        reg["zeros_conferem"] = abs(za[0]) <= za[1] + abs(ze[0]) * Decimal("1e-3") and \
            abs(zb[0]) <= zb[1] + abs(ze[0]) * Decimal("1e-3")
    except Exception as ex:  # noqa: BLE001
        reg["erro"] = str(ex)[:300]
    json.dump(out, open(SAI, "w"), ensure_ascii=False, indent=1)
print(json.dumps(out, ensure_ascii=False, indent=1)[:5000])
