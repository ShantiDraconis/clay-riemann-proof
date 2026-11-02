"""Zeros de ζ na faixa logo acima da verificação rigorosa publicada, certificados com Arb (FLINT 3).

    python3 janelas.py ./zeros resultados/ [orcamento_s]

Alturas (exatas, em texto):

* T_PT = 3 000 175 332 800 — fim da verificação de Platt & Trudgian (2021): até essa altura há exatamente
  12 363 153 437 138 zeros, todos em Re s = 1/2.
* g_b = 3 000 175 337 471,5 — fim de um certificado de 20 000 zeros depois de T_PT citado em out/2026 (não localizado
  aqui; a faixa (T_PT, g_b] é recalculada, de modo que o resultado não depende dele).
* T_fim = g_b + 5000 — a faixa nova pedida, (g_b, g_b + 5000].

O que sai:

1. N(T) exato em T_PT, g_b e T_fim (acb_dirichlet_zeta_nzeros: contagem de Turing com aritmética intervalar).
2. Todos os zeros de índice N(T_PT)+1 … N(T_fim), pelo método local de Platt (acb_dirichlet_platt_local_hardy_z_zeros),
   cada um como bola [t ± r] com Z(t) = 0, isto é, em Re s = 1/2.
3. Conferência: o número de zeros na reta com altura em (a, b] é igual a N(b) − N(a) — a contagem de TODOS os zeros
   da faixa crítica 0 < Re s < 1 nessas alturas. Se houvesse um zero fora da reta (que viria com o par 1 − ρ̄ na mesma
   altura), N(b) − N(a) seria maior. Igualdade = nenhum zero fora da reta em 0 < Re s < 1, a < Im s ≤ b.

Nada disto é prova de RH: é a verificação finita, levada 5000 unidades além.
"""
import gzip
import json
import math
import re
import subprocess
import sys
import time
from decimal import Decimal
from pathlib import Path

BIN = sys.argv[1]
OUT = Path(sys.argv[2])
OUT.mkdir(parents=True, exist_ok=True)
ORCAMENTO = float(sys.argv[3]) if len(sys.argv) > 3 else 4.5 * 3600
T_PT, N_PT_PUBLICADO = "3000175332800", 12363153437138
G_B = "3000175337471.5"
T_FIM = str(Decimal(G_B) + 5000)
INICIO = time.time()
estado = {"fonte": "FLINT/Arb: acb_dirichlet_zeta_nzeros, acb_dirichlet_platt_local_hardy_z_zeros",
          "T_PT": T_PT, "N_PT_publicado": str(N_PT_PUBLICADO), "g_b": G_B, "T_fim": T_FIM, "blocos": []}


def roda(*args, timeout=4 * 3600):
    t0 = time.time()
    r = subprocess.run([BIN, *map(str, args)], capture_output=True, text=True, timeout=timeout)
    if r.returncode:
        raise RuntimeError(f"{args}: código {r.returncode}: {r.stderr[-500:]}")
    return json.loads(r.stdout), time.time() - t0


def bola(s):
    m = re.match(r"\[?\s*([0-9.eE+-]+)\s*(?:\+/-\s*([0-9.eE+-]+))?\s*\]?", s)
    return Decimal(m.group(1)), Decimal(m.group(2) or "0")


def inteiro(s):
    """N(T) sai do Arb como bola exata ("12362403019661.0000…" sem raio): confere que é inteiro exato."""
    meio, raio = bola(s)
    if raio != 0 or meio != meio.to_integral_value():
        raise ValueError(f"N(T) não é inteiro exato: {s}")
    return int(meio)


def grava():
    estado["segundos"] = round(time.time() - INICIO, 1)
    (OUT / "zeros.json").write_text(json.dumps(estado, ensure_ascii=False, indent=1) + "\n")


def nz(T):
    r, seg = roda("nzeros", T, 256)
    return inteiro(r["N"]), r["N"], round(seg, 1)


def _registra_erro(tipo, valor, tb):
    import traceback
    estado["erro"] = "".join(traceback.format_exception(tipo, valor, tb))[-1500:]
    grava()
    sys.__excepthook__(tipo, valor, tb)


sys.excepthook = _registra_erro


# 1. contagens exatas
for nome, T in (("T_PT", T_PT), ("g_b", G_B), ("T_fim", T_FIM)):
    N, txt, seg = nz(T)
    estado[f"N({nome})"] = {"T": T, "N": str(N), "arb": txt, "segundos": seg}
    grava()
N_PT, N_GB, N_FIM = (int(estado[f"N({k})"]["N"]) for k in ("T_PT", "g_b", "T_fim"))
estado["N_PT_confere_com_Platt_Trudgian"] = N_PT == N_PT_PUBLICADO
estado["zeros_entre_T_PT_e_g_b"] = N_GB - N_PT
estado["zeros_entre_g_b_e_T_fim"] = N_FIM - N_GB
grava()

# 2. todos os zeros de N_PT+1 a N_FIM; cada bloco pede MARGEM zeros a mais de cada lado e fica com o miolo (os zeros
# da borda de um bloco do método local saem com bola maior)
MARGEM = 40
zeros = []  # (índice, meio, raio)
n = N_PT + 1
while n <= N_FIM and time.time() - INICIO < ORCAMENTO:
    k = min(5000, N_FIM - n + 1)
    r, seg = roda("platt", n - MARGEM, k + 2 * MARGEM, 256)
    zs = [bola(z) for z in r["zeros"]][MARGEM:MARGEM + k]
    estado["blocos"].append({"n": str(n), "pedidos": k, "achados": len(zs), "segundos": round(seg, 1)})
    if not zs:
        break
    zeros += [(n + i, m, rr) for i, (m, rr) in enumerate(zs)]
    n += len(zs)
    grava()

# 2b. zeros cuja bola encosta na do vizinho (ou com raio > 1e-6): de novo pelo método geral (Gram/Rosser/Turing)
def ruins(zs):
    out = set()
    for j, (_, m, rr) in enumerate(zs):
        if rr > Decimal("1e-6"):
            out.add(j)
        if j + 1 < len(zs) and m + rr >= zs[j + 1][1] - zs[j + 1][2]:
            out |= {j, j + 1}
    return sorted(out)


rr0 = ruins(zeros)
estado["refinamento"] = {"antes": len(rr0), "refinados": 0}
for j in rr0:
    if time.time() - INICIO > ORCAMENTO:
        break
    i = zeros[j][0]
    try:
        r, seg = roda("hardy", i, 1, 256, timeout=1800)
        m, rr = bola(r["zeros"][0])
        zeros[j] = (i, m, rr)
        estado["refinamento"]["refinados"] += 1
    except Exception as ex:  # noqa: BLE001
        estado["refinamento"].setdefault("erros", []).append(f"{i}: {str(ex)[:200]}")
    grava()
estado["refinamento"]["depois"] = len(ruins(zeros))
grava()

with gzip.open(OUT / "zeros_faixa.csv.gz", "wt") as f:
    f.write("indice,ordenada_meio,raio\n")
    for i, m, rr in zeros:
        f.write(f"{i},{m},{rr}\n")

# 3. conferências
completo = bool(zeros) and zeros[-1][0] == N_FIM
alturas = [m for _, m, _ in zeros]
crescente = all(a + ra < b - rb for (_, a, ra), (_, b, rb) in zip(zeros, zeros[1:]))
gb, tfim, tpt = Decimal(G_B), Decimal(T_FIM), Decimal(T_PT)
na_faixa_nova = [z for z in zeros if gb < z[1] <= tfim]
na_faixa_antiga = [z for z in zeros if tpt < z[1] <= gb]
fronteiras_ok = (completo and zeros[0][1] - zeros[0][2] > tpt and zeros[-1][1] + zeros[-1][2] <= tfim
                 and all(not (z[1] - z[2] <= gb < z[1] + z[2]) for z in zeros))
estado["conferencia"] = {
    "todos_os_indices_calculados": completo,
    "zeros_calculados": len(zeros),
    "bolas_disjuntas_e_em_ordem": crescente,
    "nenhuma_bola_cruza_g_b_e_extremos_dentro": fronteiras_ok,
    "zeros_na_reta_em_(T_PT,g_b]": len(na_faixa_antiga),
    "zeros_na_reta_em_(g_b,T_fim]": len(na_faixa_nova),
    "igual_a_N(g_b)-N(T_PT)": len(na_faixa_antiga) == N_GB - N_PT,
    "igual_a_N(T_fim)-N(g_b)": len(na_faixa_nova) == N_FIM - N_GB,
    "maior_raio": str(max((z[2] for z in zeros), default=0)),
    "menor_distancia_entre_zeros": str(min((b - a for a, b in zip(alturas, alturas[1:])), default=0)),
    "primeiro_zero_da_faixa_nova": str(na_faixa_nova[0][1]) if na_faixa_nova else None,
    "ultimo_zero_da_faixa_nova": str(na_faixa_nova[-1][1]) if na_faixa_nova else None,
}
estado["conclusao"] = (
    "nenhum zero fora da reta em 0 < Re s < 1 com T_PT < Im s ≤ T_fim (contagem fecha)"
    if completo and crescente and fronteiras_ok and estado["conferencia"]["igual_a_N(g_b)-N(T_PT)"]
    and estado["conferencia"]["igual_a_N(T_fim)-N(g_b)"] else "inconclusivo: ver conferencia")
grava()
print(json.dumps({k: v for k, v in estado.items() if k != "blocos"}, ensure_ascii=False, indent=1))
if estado["conclusao"].startswith("inconclusivo"):
    sys.exit(1)
