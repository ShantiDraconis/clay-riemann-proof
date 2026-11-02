"""Janelas de zeros de ζ acima de 3·10¹² (Platt–Trudgian 2021), certificadas com Arb (FLINT 3).

    python3 janelas.py ./zeros resultados/

1. N(3·10¹²) exato (contagem de Turing no Arb).
2. Bloco contíguo: os zeros de índice N+1, N+2, … — cada um é o próximo zero de ζ contando TODOS os zeros (na reta e
   fora dela), e sai como zero de Z(t), isto é, em Re s = 1/2. Junto com Platt–Trudgian, a hipótese de Riemann fica
   conferida até a altura do último zero do bloco.
3. Amostras em alturas maiores (10¹³ … 10²²): blocos de zeros consecutivos em torno do índice N(T) aproximado.

Nada disto é prova de RH: é a mesma verificação finita que o mundo fez até 3·10¹², levada um pouco além.
"""
import json
import math
import re
import subprocess
import sys
import time
from pathlib import Path

BIN = sys.argv[1]
OUT = Path(sys.argv[2])
OUT.mkdir(parents=True, exist_ok=True)
ORCAMENTO = float(sys.argv[3]) if len(sys.argv) > 3 else 4.5 * 3600  # segundos para começar blocos novos
T_PT = "3000000000000"
INICIO = time.time()
estado = {"fonte": "FLINT/Arb: acb_dirichlet_zeta_nzeros, acb_dirichlet_platt_local_hardy_z_zeros",
          "verificado_antes": "Platt & Trudgian (2021): todos os zeros com 0 < Im s ≤ 3·10¹² estão em Re s = 1/2",
          "blocos": []}


def roda(*args, timeout=3 * 3600):
    t0 = time.time()
    r = subprocess.run([BIN, *map(str, args)], capture_output=True, text=True, timeout=timeout)
    if r.returncode:
        raise RuntimeError(f"{args}: código {r.returncode}: {r.stderr[-500:]}")
    return json.loads(r.stdout), time.time() - t0


def bola(s):
    m = re.match(r"\[?\s*([0-9.eE+-]+)\s*(?:\+/-\s*([0-9.eE+-]+))?\s*\]?", s)
    return m.group(1), (m.group(2) or "0")


def grava():
    estado["segundos"] = round(time.time() - INICIO, 1)
    (OUT / "zeros.json").write_text(json.dumps(estado, ensure_ascii=False, indent=1) + "\n")


def n_aprox(T):
    """N(T) ≈ (T/2π)·log(T/2πe) + 7/8 (Riemann–von Mangoldt sem S(T)): só para escolher o índice da amostra."""
    x = T / (2 * math.pi)
    return int(x * math.log(x / math.e) + 7 / 8)


def bloco(n, total, passo, rotulo, prec=128):
    feitos, ult = 0, None
    while feitos < total and time.time() - INICIO < ORCAMENTO:
        k = min(passo, total - feitos)
        r, seg = roda("platt", n + feitos, k, prec)
        zs = [bola(z) for z in r["zeros"]]
        if not zs:
            estado["blocos"].append({"rotulo": rotulo, "n": str(n + feitos), "achados": 0, "segundos": round(seg, 1)})
            break
        alturas = [float(m) for m, _ in zs]
        crescente = all(a < b for a, b in zip(alturas, alturas[1:]))
        estado["blocos"].append({
            "rotulo": rotulo, "metodo": "platt", "n_primeiro": str(n + feitos), "n_ultimo": str(n + feitos + len(zs) - 1),
            "achados": len(zs), "pedidos": k, "segundos": round(seg, 1), "ordenadas_crescentes": crescente,
            "primeiro": {"t": zs[0][0], "raio": zs[0][1]}, "ultimo": {"t": zs[-1][0], "raio": zs[-1][1]},
            "maior_raio": max(zs, key=lambda z: float(z[1]))[1],
            "menor_intervalo_entre_zeros": min((b - a for a, b in zip(alturas, alturas[1:])), default=None),
            "zeros": [m for m, _ in zs] if len(zs) <= 400 else None,
        })
        feitos += len(zs)
        ult = zs[-1][0]
        grava()
    return feitos, ult


r, seg = roda("nzeros", T_PT, 256)
N = int(bola(r["N"])[0])
estado["N_3e12"] = {"N": str(N), "texto": r["N"], "segundos": round(seg, 1)}
grava()

# 2. bloco contíguo logo acima de 3·10¹²
feitos, ult = bloco(N + 1, int(sys.argv[4]) if len(sys.argv) > 4 else 200000, 20000, "contiguo_acima_de_3e12")
estado["contiguo"] = {"de_indice": str(N + 1), "zeros": feitos, "ate_altura": ult}
grava()

# 3. amostras em alturas maiores
for e in (13, 14, 15, 16, 18, 20, 22):
    if time.time() - INICIO > ORCAMENTO:
        break
    try:
        bloco(n_aprox(10.0 ** e), 1000, 1000, f"amostra_1e{e}")
    except Exception as ex:  # noqa: BLE001
        estado["blocos"].append({"rotulo": f"amostra_1e{e}", "erro": str(ex)[:300]})
    grava()
print(json.dumps({k: v for k, v in estado.items() if k != "blocos"}, ensure_ascii=False, indent=1))
