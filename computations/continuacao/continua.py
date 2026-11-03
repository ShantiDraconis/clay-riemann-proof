"""Continuação contígua da faixa certificada: zeros de ζ logo acima de 3 000 175 342 471,5, com Arb (FLINT 3).

    python3 continua.py ./zeros saida/ I [orcamento_s]

É aqui que estaria o PRIMEIRO zero fora da reta, se existisse: tudo até C0 já foi conferido (Platt–Trudgian, a seção 13
do README e as execuções anteriores desta continuação, listadas em `inicio.json`), e
`Continuacao.primeiro_fora_acima_continuacao` diz que o primeiro zero fora da reta, se existir, tem altura maior.
C0 e N(C0) vêm de `inicio.json`. A faixa I (0, 1, 2, …) é (C0 + I·H, C0 + (I+1)·H], H = 120 000.

O que sai, para a faixa (a, b]:

1. N(a) e N(b) exatos (acb_dirichlet_zeta_nzeros: contagem de Turing com aritmética intervalar). N conta TODOS os zeros
   com 0 < Re s < 1, na reta ou fora dela.
2. Todos os zeros de índice N(a)+1 … N(b) pelo método local de Platt (acb_dirichlet_platt_local_hardy_z_zeros), cada um
   como bola [t ± r] com Z(t) = 0, isto é, em Re s = ½.
3. A busca: se os zeros achados na reta em (a, b] forem menos que N(b) − N(a), a diferença são zeros fora da reta
   (em pares ρ, 1 − ρ̄ na mesma altura). Se um bloco do método local não fechar, o índice é registrado em `falhas`:
   é ali que se procura com caixas e o princípio do argumento.

Se o orçamento acabar antes, a parte calculada é conferida com N no fim dela (`parcial`).
Nada disto é prova de RH: é a verificação finita levada adiante.
"""
import gzip
import json
import re
import subprocess
import sys
import time
from decimal import Decimal
from pathlib import Path

BIN = sys.argv[1]
OUT = Path(sys.argv[2])
I = int(sys.argv[3])
ORCAMENTO = float(sys.argv[4]) if len(sys.argv) > 4 else 18500
OUT.mkdir(parents=True, exist_ok=True)
INICIO = json.loads((Path(__file__).parent / "inicio.json").read_text())
C0, H = Decimal(INICIO["C0"]), Decimal(120000)
N_C0_ANTERIOR = int(INICIO["N(C0)"])  # N(C0) calculado pela execução anterior
A, B = C0 + I * H, C0 + (I + 1) * H
PREC, BLOCO, MARGEM = 256, 5000, 40
T_INICIO = time.time()
estado = {"fonte": "FLINT/Arb: acb_dirichlet_zeta_nzeros, acb_dirichlet_platt_local_hardy_z_zeros",
          "faixa": I, "a": str(A), "b": str(B), "blocos": [], "falhas": []}


def grava():
    estado["segundos"] = round(time.time() - T_INICIO, 1)
    (OUT / f"faixa{I}.json").write_text(json.dumps(estado, ensure_ascii=False, indent=1) + "\n")


def _erro(tipo, valor, tb):
    import traceback
    estado["erro"] = "".join(traceback.format_exception(tipo, valor, tb))[-1500:]
    grava()
    sys.__excepthook__(tipo, valor, tb)


sys.excepthook = _erro


def roda(*args, timeout=3 * 3600):
    t0 = time.time()
    r = subprocess.run([BIN, *map(str, args)], capture_output=True, text=True, timeout=timeout)
    if r.returncode:
        raise RuntimeError(f"{args}: código {r.returncode}: {r.stderr[-500:]}")
    return json.loads(r.stdout), time.time() - t0


def bola(s):
    m = re.match(r"\[?\s*([0-9.eE+-]+)\s*(?:\+/-\s*([0-9.eE+-]+))?\s*\]?", s)
    return Decimal(m.group(1)), Decimal(m.group(2) or "0")


def nz(T):
    r, seg = roda("nzeros", T, PREC)
    meio, raio = bola(r["N"])
    if raio != 0 or meio != meio.to_integral_value():
        raise ValueError(f"N({T}) não é inteiro exato: {r['N']}")
    return int(meio), round(seg, 1)


# 1. contagens exatas nas pontas
Na, sa = nz(A)
Nb, sb = nz(B)
estado.update({"N(a)": str(Na), "N(b)": str(Nb), "zeros_esperados": Nb - Na, "segundos_nzeros": [sa, sb]})
if I == 0:
    estado["N(C0)_confere_com_a_execucao_anterior"] = Na == N_C0_ANTERIOR
grava()

# 2. todos os zeros de N(a)+1 a N(b); cada bloco pede MARGEM zeros a mais de cada lado e fica com o miolo
zeros = []  # (índice, meio, raio)
n = Na + 1
while n <= Nb and time.time() - T_INICIO < ORCAMENTO:
    k = min(BLOCO, Nb - n + 1)
    r, seg = roda("platt", n - MARGEM, k + 2 * MARGEM, PREC)
    zs = [bola(z) for z in r["zeros"]][MARGEM:MARGEM + k]
    if len(zs) < k:  # o bloco não fechou: tenta em pedaços menores antes de registrar a falha
        estado["falhas"].append({"n": str(n), "pedidos": k, "achados": len(zs), "achados_brutos": r["achados"]})
        k2 = max(1, k // 10)
        r, seg2 = roda("platt", n - MARGEM, k2 + 2 * MARGEM, PREC)
        zs = [bola(z) for z in r["zeros"]][MARGEM:MARGEM + k2]
        seg += seg2
        estado["falhas"][-1]["repeticao"] = {"pedidos": k2, "achados": len(zs)}
        if len(zs) < k2:
            estado["parou_em"] = str(n)
            grava()
            break
        k = k2
    zeros += [(n + i, m, rr) for i, (m, rr) in enumerate(zs)]
    estado["blocos"].append({"n": str(n), "pedidos": k, "achados": len(zs), "segundos": round(seg, 1)})
    n += len(zs)
    if len(estado["blocos"]) % 10 == 0:
        grava()
grava()

with gzip.open(OUT / f"zeros{I}.csv.gz", "wt") as f:
    f.write("indice,ordenada_meio,raio\n")
    for i, m, rr in zeros:
        f.write(f"{i},{m},{rr}\n")

# 3. conferências
completo = bool(zeros) and zeros[-1][0] == Nb
em_ordem = all(a + ra < b - rb for (_, a, ra), (_, b, rb) in zip(zeros, zeros[1:]))
indices_seguidos = all(j == i + 1 for (i, _, _), (j, _, _) in zip(zeros, zeros[1:]))
dentro = bool(zeros) and zeros[0][1] - zeros[0][2] > A and (not completo or zeros[-1][1] + zeros[-1][2] <= B)
conf = {"todos_os_indices": completo, "zeros_na_reta": len(zeros), "bolas_disjuntas_e_em_ordem": em_ordem,
        "indices_seguidos": indices_seguidos, "extremos_dentro_da_faixa": dentro,
        "maior_raio": str(max((z[2] for z in zeros), default=0))}
if completo:
    conf["na_reta_igual_a_N(b)-N(a)"] = len([z for z in zeros if A < z[1] <= B]) == Nb - Na
    conf["deficit_(zeros_fora_da_reta)"] = (Nb - Na) - len([z for z in zeros if A < z[1] <= B])
    fim_certificado = B
elif zeros:
    # parcial: confere N logo acima do último zero calculado
    _, m, rr = zeros[-1]
    T2 = m + rr + Decimal("1e-12")
    N2, _ = nz(T2)
    conf["parcial"] = {"T": str(T2), "N(T)": str(N2), "ultimo_indice": str(zeros[-1][0]),
                       "na_reta_igual_a_N(T)-N(a)": N2 - Na == len(zeros)}
    fim_certificado = T2 if N2 - Na == len(zeros) else None
else:
    fim_certificado = None
estado["conferencia"] = conf
ok = em_ordem and indices_seguidos and dentro and (
    conf.get("na_reta_igual_a_N(b)-N(a)") or conf.get("parcial", {}).get("na_reta_igual_a_N(T)-N(a)"))
estado["certificado_ate"] = str(fim_certificado) if ok and fim_certificado else None
estado["conclusao"] = (f"nenhum zero fora da reta em 0 < Re s < 1, {A} < Im s ≤ {fim_certificado}" if ok
                       else "inconclusivo: ver conferencia e falhas")
grava()
print(json.dumps({k: v for k, v in estado.items() if k != "blocos"}, ensure_ascii=False, indent=1))
