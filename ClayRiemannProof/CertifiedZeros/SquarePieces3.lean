import ClayRiemannProof.CertifiedZeros.SquarePieces2

/-!
# Peças do bordo do quadrado, arquivo 3 de 3: aresta de cima Im = 727/50

O quadrado é `[1/10, 9/10] × [1373/100, 727/50]`, que contém o disco `|s − z₀| ≤ 2/5` em volta de
`z₀ = ½ + 14,1347251417 i`. Cada peça é um retângulo fino em volta de um trecho de aresta, certificado por
`UpperBound.peca_sup`: `‖ζ(c)‖ + (B/r)h ≤ 1,0` em todos os centros (`chkS`, `decide +kernel`, sem
`native_decide`), com `B = cotaQ` na região de Cauchy. Gerado por `computations/contorno/gera_pecas_lean.py` a partir
de `planeja_quadrado.py`. Arquivo novo (não vem do ATK).
-/

open Complex

namespace ClayRiemannProof.CertifiedZeros.SquarePieces3

open ClayRiemannProof.CertifiedZeros.Rectangle ClayRiemannProof.CertifiedZeros.UpperBound

set_option maxRecDepth 100000 in
/-- `[0,1000; 0,2000] × [14,5399; 14,5401]`: 10×1 centros, r = 0,0989, B = 7,642, máx |ζ(c)| ≈ 0,548 ≤ u = 0,614. -/
theorem C1 : ∀ z ∈ ret (((1 / 10 : ℚ)) : ℝ) (((1 / 5 : ℚ)) : ℝ) (((145399 / 10000 : ℚ)) : ℝ) (((145401 / 10000 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (1 / 10 : ℚ)) (s1 := (1 / 5 : ℚ)) (a := (145399 / 10000 : ℚ)) (b := (145401 / 10000 : ℚ)) (r := (989 / 10000 : ℚ)) (B := (3821 / 500 : ℚ))
    (hs := (1 / 200 : ℚ)) (ht := (1 / 10000 : ℚ)) (h := (50011 / 10000000 : ℚ)) (u := (303407969 / 494500000 : ℚ)) (U := (1 : ℚ)) (R := (733 / 50 : ℚ)) (d := (14441 / 1000 : ℚ))
    (ns := 10) (nt := 1) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,2000; 0,3000] × [14,5399; 14,5401]`: 5×1 centros, r = 0,1900, B = 7,670, máx |ζ(c)| ≈ 0,460 ≤ u = 0,596. -/
theorem C2 : ∀ z ∈ ret (((1 / 5 : ℚ)) : ℝ) (((3 / 10 : ℚ)) : ℝ) (((145399 / 10000 : ℚ)) : ℝ) (((145401 / 10000 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (1 / 5 : ℚ)) (s1 := (3 / 10 : ℚ)) (a := (145399 / 10000 : ℚ)) (b := (145401 / 10000 : ℚ)) (r := (19 / 100 : ℚ)) (B := (767 / 100 : ℚ))
    (hs := (1 / 100 : ℚ)) (ht := (1 / 10000 : ℚ)) (h := (50003 / 5000000 : ℚ)) (u := (56647699 / 95000000 : ℚ)) (U := (1 : ℚ)) (R := (59 / 4 : ℚ)) (d := (143499 / 10000 : ℚ))
    (ns := 5) (nt := 1) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,3000; 0,6000] × [14,5399; 14,5401]`: 15×1 centros, r = 0,2900, B = 7,709, máx |ζ(c)| ≈ 0,396 ≤ u = 0,734. -/
theorem C3 : ∀ z ∈ ret (((3 / 10 : ℚ)) : ℝ) (((3 / 5 : ℚ)) : ℝ) (((145399 / 10000 : ℚ)) : ℝ) (((145401 / 10000 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (3 / 10 : ℚ)) (s1 := (3 / 5 : ℚ)) (a := (145399 / 10000 : ℚ)) (b := (145401 / 10000 : ℚ)) (r := (29 / 100 : ℚ)) (B := (7709 / 1000 : ℚ))
    (hs := (1 / 100 : ℚ)) (ht := (1 / 10000 : ℚ)) (h := (50003 / 5000000 : ℚ)) (u := (1064526873 / 1450000000 : ℚ)) (U := (1 : ℚ)) (R := (1487 / 100 : ℚ)) (d := (142499 / 10000 : ℚ))
    (ns := 15) (nt := 1) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,6000; 0,9000] × [14,5399; 14,5401]`: 6×1 centros, r = 0,4000, B = 7,757, máx |ζ(c)| ≈ 0,387 ≤ u = 0,515. -/
theorem C4 : ∀ z ∈ ret (((3 / 5 : ℚ)) : ℝ) (((9 / 10 : ℚ)) : ℝ) (((145399 / 10000 : ℚ)) : ℝ) (((145401 / 10000 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (3 / 5 : ℚ)) (s1 := (9 / 10 : ℚ)) (a := (145399 / 10000 : ℚ)) (b := (145401 / 10000 : ℚ)) (r := (2 / 5 : ℚ)) (B := (7757 / 1000 : ℚ))
    (hs := (1 / 40 : ℚ)) (ht := (1 / 10000 : ℚ)) (h := (250003 / 10000000 : ℚ)) (u := (2060726729 / 4000000000 : ℚ)) (U := (1 : ℚ)) (R := (1501 / 100 : ℚ)) (d := (141399 / 10000 : ℚ))
    (ns := 6) (nt := 1) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

end ClayRiemannProof.CertifiedZeros.SquarePieces3
