"""Compara todas as varreduras, mede a tendência de λ e ataca os pares mais frágeis com contagem de Turing local.

    python3 ataque.py ./zeros ENTRADA/ SAIDA/

ENTRADA tem o que as outras execuções gravaram (fronteira.json e varreduras/*.json da branch resultados-fronteira,
alturas.json de resultados-alturas, zeros.json de resultados-zeros). O que sai:

1. **Tendência**: para cada varredura, (altura T, zeros N, s_min, λ do par mais frágil, zeros por segundo). Pela
   repulsão do GUE e pela cota de Csordas–Smith–Varga, λ_min ≈ −½·(9/(π²N))^{2/3}/ρ², ρ = log(T/2π)/2π. A tendência
   vai a 0⁻ quando N·ρ³ cresce e **não cruza 0 em nenhum N finito**: um zero fora da reta não seria a continuação
   da tendência, seria uma quebra dela (um par com λ ≥ 0, ou uma contagem de Turing que não fecha).
2. **Onde atacar**: a altura que dá o maior N·ρ³ por hora (zeros por segundo medidos em cada altura) e quantos zeros
   e horas seriam precisos ali para chegar a λ = −10⁻⁷, −10⁻⁹ e ao recorde −1,14541·10⁻¹¹ (Saouter–Gourdon–Demichel).
3. **Ataque local**: para cada um dos pares mais frágeis, N(T) exato nos pontos médios antes e depois do par
   (contagem de Turing): N(T_b) − N(T_a) = 2 quer dizer que, nessa faixa de alturas, os dois zeros da reta são os
   únicos zeros de ζ em 0 < Re s < 1 — nenhum quarteto escondido ali.

Cálculo fora do kernel; nada aqui prova ou refuta RH.
"""
import json
import math
import re
import subprocess
import sys
import time
from decimal import Decimal, getcontext
from pathlib import Path

getcontext().prec = 80
BIN, ENT, SAI = sys.argv[1], Path(sys.argv[2]), Path(sys.argv[3])
SAI.mkdir(parents=True, exist_ok=True)
INICIO = time.time()


def ler(p):
    try:
        return json.loads(Path(p).read_text())
    except Exception:  # noqa: BLE001
        return None


def rho(T):
    return math.log(T / (2 * math.pi)) / (2 * math.pi)


def bola(s):
    m = re.match(r"\[?\s*([0-9.eE+-]+)\s*(?:\+/-\s*([0-9.eE+-]+))?\s*\]?", s)
    return Decimal(m.group(1)), Decimal(m.group(2) or "0")


def roda(*args, timeout=3 * 3600):
    r = subprocess.run([BIN, *map(str, args)], capture_output=True, text=True, timeout=timeout)
    if r.returncode:
        raise RuntimeError(r.stderr[-300:])
    return json.loads(r.stdout)


# 1. tendência: um ponto por varredura
pontos = []
z = ler(ENT / "zeros.json")
if z and z.get("conferencia"):
    N = z["conferencia"]["zeros_calculados"]
    seg = sum(b.get("segundos", 0) for b in z.get("blocos", [])) or z.get("segundos", 1)
    pontos.append({"origem": "faixa T_PT…g_b+5000", "T": 3.0001753e12, "N": N, "s_min": 0.0341842,
                   "lambda": -3.1919e-05, "zeros_por_s": N / seg})
a = ler(ENT / "alturas.json")
for j in (a or {}).get("janelas", []):
    st = j.get("estatistica")
    if not st:
        continue
    T = 10.0 ** int(j["altura"].split("e")[1])
    lam = st["pares_mais_frageis"][0]["lambda_CSV"] if st.get("pares_mais_frageis") else None
    pontos.append({"origem": f"janela {j['altura']}", "T": T, "N": j["N"], "s_min": st["s_min"], "lambda": lam,
                   "zeros_por_s": (j["N"] + 82) / j["segundos_zeros"] if j.get("segundos_zeros") else None})
for f in sorted((ENT / "varreduras").glob("varre_*.json")) if (ENT / "varreduras").is_dir() else []:
    v = ler(f)
    if not v or not v.get("pares_analisados"):
        continue
    T = 10.0 ** v["expoente"]
    pontos.append({"origem": f"varredura 10^{v['expoente']} +{v['deslocamento']}", "T": T, "N": v["pares_analisados"],
                   "s_min": v.get("s_min"), "lambda": v["topo"][0]["lambda_CSV"] if v.get("topo") else None,
                   "zeros_por_s": v["zeros_varridos"] / v["segundos"] if v.get("segundos") else None})
for p in pontos:
    p["rho"] = rho(p["T"])
    p["lambda_previsto"] = -0.5 * (9 / (math.pi ** 2 * p["N"])) ** (2 / 3) / p["rho"] ** 2
    p["razao_obs_prev"] = (p["lambda"] / p["lambda_previsto"]) if p.get("lambda") else None

# 2. onde atacar: zeros por segundo em função da altura (ajuste log-log) e mérito N·ρ³ por hora
alt = {}
for p in pontos:
    if p.get("zeros_por_s"):
        alt.setdefault(p["T"], []).append(p["zeros_por_s"])
taxa = {T: sum(v) / len(v) for T, v in alt.items()}
ajuste = None
if len(taxa) >= 2:
    xs = [math.log(T) for T in taxa]
    ys = [math.log(v) for v in taxa.values()]
    mx, my = sum(xs) / len(xs), sum(ys) / len(ys)
    b = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / max(sum((x - mx) ** 2 for x in xs), 1e-30)
    ajuste = {"expoente_da_taxa": b, "constante": math.exp(my - b * mx)}
alvos = []
for e in range(13, 23):
    T = 10.0 ** e
    if T in taxa:
        z_s = taxa[T]
    elif ajuste:
        z_s = ajuste["constante"] * T ** ajuste["expoente_da_taxa"]
    else:
        continue
    r = rho(T)
    linha = {"altura": f"1e{e}", "zeros_por_s": z_s, "merito_por_hora": z_s * 3600 * r ** 3}
    for lam in (1e-7, 1e-9, 1.14541e-11):
        N = 9 / math.pi ** 2 * (2 * lam * r * r) ** -1.5
        linha[f"zeros_para_{lam:g}"] = N
        linha[f"horas_de_1_job_para_{lam:g}"] = N / z_s / 3600
    alvos.append(linha)
alvos.sort(key=lambda l: -l["merito_por_hora"])

# 3. ataque local nos pares mais frágeis: contagem de Turing no intervalo do par
fr = ler(ENT / "fronteira.json") or {}
cands = list(fr.get("mais_frageis", []))
if a:
    for j in a.get("janelas", []):
        for c in (j.get("estatistica") or {}).get("pares_mais_frageis", [])[:3]:
            if c.get("lambda_CSV") is not None:
                cands.append({"indice": str(int(j["n0"]) + c["posicao"]), "gamma_k": c["gamma_k"],
                              "lambda_CSV": c["lambda_CSV"], "s": c["s"], "expoente": int(j["altura"].split("e")[1])})
cands.sort(key=lambda c: -c["lambda_CSV"])
ataques = []
for c in cands[:12]:
    if time.time() - INICIO > 4 * 3600:
        break
    k = int(c["indice"])
    reg = {"indice": c["indice"], "gamma_k": c["gamma_k"], "lambda_CSV": c["lambda_CSV"], "s": c.get("s"),
           "expoente": c.get("expoente")}
    try:
        M = 40
        r = roda("platt", k - 1 - M, 4 + 2 * M, 320)
        zs = [bola(x) for x in r["zeros"]][M:M + 4]  # γ_{k−1}, γ_k, γ_{k+1}, γ_{k+2}
        Ta = (zs[0][0] + zs[1][0]) / 2
        Tb = (zs[2][0] + zs[3][0]) / 2
        na = roda("nzeros", f"{Ta:.15f}", 320)["N"]
        nb = roda("nzeros", f"{Tb:.15f}", 320)["N"]
        Na, Nb = int(bola(na)[0]), int(bola(nb)[0])
        reg.update({"gamma_k_recalculado": str(zs[1][0]), "gamma_k1": str(zs[2][0]), "T_a": f"{Ta:.15f}",
                    "T_b": f"{Tb:.15f}", "N(T_a)": str(Na), "N(T_b)": str(Nb),
                    "dois_zeros_e_so": Nb - Na == 2 and Na == k - 1,
                    "conclusao": ("os dois zeros do par são os únicos de ζ em 0 < Re s < 1 com T_a < Im s ≤ T_b: "
                                  "nenhum quarteto ali") if Nb - Na == 2 and Na == k - 1 else "ver números"})
    except Exception as ex:  # noqa: BLE001
        reg["erro"] = str(ex)[:300]
    ataques.append(reg)
    (SAI / "ataque.json").write_text(json.dumps({"pontos": pontos, "ajuste_taxa": ajuste, "onde_atacar": alvos,
                                                  "ataques": ataques}, ensure_ascii=False, indent=1) + "\n")

out = {"pontos": pontos, "ajuste_taxa": ajuste, "onde_atacar": alvos, "ataques": ataques,
       "leitura": ("λ_min segue −½(9/(π²N))^{2/3}/ρ²: vai a 0⁻ com N·ρ³ e não cruza 0 em N finito. Um zero fora da "
                   "reta apareceria como quebra (λ ≥ 0 ou contagem que não fecha), não como continuação da curva.")}
(SAI / "ataque.json").write_text(json.dumps(out, ensure_ascii=False, indent=1) + "\n")
md = ["# Ataque: tendência, escala e contagem local nos pares mais frágeis", "",
      "| origem | T | N | s_min | λ observado | λ previsto | obs/prev | zeros/s |", "|---|---|---|---|---|---|---|---|"]
for p in pontos:
    md.append(f"| {p['origem']} | {p['T']:.3g} | {p['N']} | {p['s_min']:.5f} | "
              f"{(p['lambda'] or 0):.3e} | {p['lambda_previsto']:.3e} | {(p['razao_obs_prev'] or 0):.2f} | "
              f"{(p['zeros_por_s'] or 0):.1f} |")
md += ["", "| altura | zeros/s | mérito N·ρ³/h | zeros p/ −1e-7 | horas p/ −1e-7 | zeros p/ recorde | horas p/ recorde |",
       "|---|---|---|---|---|---|---|"]
for l in alvos:
    md.append(f"| {l['altura']} | {l['zeros_por_s']:.1f} | {l['merito_por_hora']:.3g} | {l['zeros_para_1e-07']:.3g} | "
              f"{l['horas_de_1_job_para_1e-07']:.3g} | {l['zeros_para_1.14541e-11']:.3g} | "
              f"{l['horas_de_1_job_para_1.14541e-11']:.3g} |")
md += ["", "| índice | γ_k | λ | N(T_a) | N(T_b) | só os dois zeros? |", "|---|---|---|---|---|---|"]
for r in ataques:
    md.append(f"| {r['indice']} | {r['gamma_k'][:30]} | {r['lambda_CSV']:.3e} | {r.get('N(T_a)', '—')} | "
              f"{r.get('N(T_b)', '—')} | {r['dois_zeros_e_so'] if 'dois_zeros_e_so' in r else 'erro: ' + r.get('erro', '')[:60]} |")
(SAI / "RESUMO.md").write_text("\n".join(md) + "\n")
print("\n".join(md))
