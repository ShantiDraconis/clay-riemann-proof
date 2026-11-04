"""Gera os arquivos Lean das peças do bordo do quadrado (cota |ζ| ≤ U), a partir do plano de planeja_quadrado.py.

    python3 gera_pecas_lean.py 0.8      (lê pecas_quadrado_0.8.json; grava ../../ClayRiemannProof/CertifiedZeros/SquarePieces{1,2,3}.lean)

Para cada peça: h racional com hs² + ht² ≤ h², u = U − (B/r)h exato, e conferência em ponto flutuante de
max |ζ(centro)| + 0,003 ≤ u antes de mandar ao kernel.
"""
import json
import math
import sys
from fractions import Fraction as Fr

import numpy as np

from zeta_em import zeta

U = Fr(sys.argv[1]) if len(sys.argv) > 1 else Fr(4, 5)
P = json.load(open(f"pecas_quadrado_{float(U)}.json"))
NE, ME, K, NT, PB = 12, 8, 16, 24, 32


def q(x):
    x = Fr(x)
    return f"({x.numerator} : ℚ)" if x.denominator == 1 else f"({x.numerator} / {x.denominator} : ℚ)"


def peca(nome, p):
    s0, s1, a, b = Fr(p["s0"]), Fr(p["s1"]), Fr(p["a"]), Fr(p["b"])
    r, B, R, d = Fr(p["r"]), Fr(p["B"]), Fr(p["R"]), Fr(p["d"])
    hs, ht, ns, nt = Fr(p["hs"]), Fr(p["ht"]), p["ns"], p["nt"]
    h = Fr(math.ceil(math.sqrt(float(hs * hs + ht * ht)) * 10 ** 7) + 1, 10 ** 7)
    assert hs * hs + ht * ht <= h * h
    u = U - B / r * h
    cs = np.array([complex(float(s0 + hs * (2 * i + 1)), float(a + ht * (2 * j + 1))) for i in range(ns) for j in range(nt)])
    mx = float(np.abs(zeta(cs)).max())
    assert mx + 0.003 <= float(u), (nome, mx, float(u))
    assert s0 + 2 * hs * ns == s1 and a + 2 * ht * nt == b
    doc = (f"/-- `[{float(s0):.4f}; {float(s1):.4f}] × [{float(a):.4f}; {float(b):.4f}]`: {ns}×{nt} centros, "
           f"r = {float(r):.4f}, B = {float(B):.3f}, máx |ζ(c)| ≈ {mx:.3f} ≤ u = {float(u):.3f}").replace(".", ",") + ". -/"
    return f"""set_option maxRecDepth 100000 in
{doc}
theorem {nome} : ∀ z ∈ ret (({q(s0)}) : ℝ) (({q(s1)}) : ℝ) (({q(a)}) : ℝ) (({q(b)}) : ℝ),
    ‖riemannZeta z‖ ≤ (({q(U)}) : ℝ) :=
  peca_sup (s0 := {q(s0)}) (s1 := {q(s1)}) (a := {q(a)}) (b := {q(b)}) (r := {q(r)}) (B := {q(B)})
    (hs := {q(hs)}) (ht := {q(ht)}) (h := {q(h)}) (u := {q(u)}) (U := {q(U)}) (R := {q(R)}) (d := {q(d)})
    (ns := {ns}) (nt := {nt}) (Nc := {p['Nc']}) (Mc := {p['Mc']}) (Ne := {NE}) (Me := {ME}) (K := {K}) (nT := {NT}) (p := {PB})
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)
""", ns * nt


CAB = """import ClayRiemannProof.CertifiedZeros.{imp}

/-!
# Peças do bordo do quadrado, arquivo {k} de 3: {oque}

O quadrado é `[1/10, 9/10] × [1373/100, 727/50]`, que contém o disco `|s − z₀| ≤ 2/5` em volta de
`z₀ = ½ + 14,1347251417 i`. Cada peça é um retângulo fino em volta de um trecho de aresta, certificado por
`UpperBound.peca_sup`: `‖ζ(c)‖ + (B/r)h ≤ {Uf}` em todos os centros (`chkS`, `decide +kernel`, sem
`native_decide`), com `B = cotaQ` na região de Cauchy. Gerado por `computations/contorno/gera_pecas_lean.py` a partir
de `planeja_quadrado.py`. Arquivo novo (não vem do ATK).
-/

open Complex

namespace ClayRiemannProof.CertifiedZeros.SquarePieces{k}

open ClayRiemannProof.CertifiedZeros.Rectangle ClayRiemannProof.CertifiedZeros.UpperBound

"""


def main():
    Uf = str(float(U)).replace(".", ",")
    esq = [p for p in P if p["tipo"] == "v" and Fr(p["s0"]) < Fr(1, 2)]
    dir_ = [p for p in P if p["tipo"] == "v" and Fr(p["s0"]) > Fr(1, 2)]
    hor = [p for p in P if p["tipo"] == "h"]
    baixo = [p for p in hor if Fr(p["a"]) < 14]
    cima = [p for p in hor if Fr(p["a"]) > 14]
    grupos = [(1, "arestas verticais Re = 1/10 e Re = 9/10", [("E", esq), ("D", dir_)]),
              (2, "aresta de baixo Im = 1373/100", [("B", baixo)]),
              (3, "aresta de cima Im = 727/50", [("C", cima)])]
    total = 0
    for k, oque, listas in grupos:
        imp = "UpperBound" if k == 1 else f"SquarePieces{k - 1}"   # em cadeia: o CI compila um de cada vez
        txt = CAB.format(k=k, oque=oque, Uf=Uf, imp=imp)
        for pref, lst in listas:
            for i, p in enumerate(lst, 1):
                t, n = peca(f"{pref}{i}", p)
                txt += t + "\n"
                total += n
        txt += f"end ClayRiemannProof.CertifiedZeros.SquarePieces{k}\n"
        open(f"../../ClayRiemannProof/CertifiedZeros/SquarePieces{k}.lean", "w").write(txt)
    print("avaliações:", total)


if __name__ == "__main__":
    main()
