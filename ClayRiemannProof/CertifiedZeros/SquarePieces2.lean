import ClayRiemannProof.CertifiedZeros.SquarePieces1

/-!
# Peças do bordo do quadrado, arquivo 2 de 3: aresta de baixo Im = 1373/100

O quadrado é `[1/10, 9/10] × [1373/100, 727/50]`, que contém o disco `|s − z₀| ≤ 2/5` em volta de
`z₀ = ½ + 14,1347251417 i`. Cada peça é um retângulo fino em volta de um trecho de aresta, certificado por
`UpperBound.peca_sup`: `‖ζ(c)‖ + (B/r)h ≤ 1,0` em todos os centros (`chkS`, `decide +kernel`, sem
`native_decide`), com `B = cotaQ` na região de Cauchy. Gerado por `computations/contorno/gera_pecas_lean.py` a partir
de `planeja_quadrado.py`. Arquivo novo (não vem do ATK).
-/

open Complex

namespace ClayRiemannProof.CertifiedZeros.SquarePieces2

open ClayRiemannProof.CertifiedZeros.Rectangle ClayRiemannProof.CertifiedZeros.UpperBound

set_option maxRecDepth 100000 in
/-- `[0,1000; 0,2000] × [13,7299; 13,7301]`: 10×1 centros, r = 0,0989, B = 7,475, máx |ζ(c)| ≈ 0,506 ≤ u = 0,622. -/
theorem B1 : ∀ z ∈ ret (((1 / 10 : ℚ)) : ℝ) (((1 / 5 : ℚ)) : ℝ) (((137299 / 10000 : ℚ)) : ℝ) (((137301 / 10000 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (1 / 10 : ℚ)) (s1 := (1 / 5 : ℚ)) (a := (137299 / 10000 : ℚ)) (b := (137301 / 10000 : ℚ)) (r := (989 / 10000 : ℚ)) (B := (299 / 40 : ℚ))
    (hs := (1 / 200 : ℚ)) (ht := (1 / 10000 : ℚ)) (h := (50011 / 10000000 : ℚ)) (u := (1069857 / 1720000 : ℚ)) (U := (1 : ℚ)) (R := (277 / 20 : ℚ)) (d := (13631 / 1000 : ℚ))
    (ns := 10) (nt := 1) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,2000; 0,3000] × [13,7299; 13,7301]`: 5×1 centros, r = 0,1900, B = 7,496, máx |ζ(c)| ≈ 0,427 ≤ u = 0,605. -/
theorem B2 : ∀ z ∈ ret (((1 / 5 : ℚ)) : ℝ) (((3 / 10 : ℚ)) : ℝ) (((137299 / 10000 : ℚ)) : ℝ) (((137301 / 10000 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (1 / 5 : ℚ)) (s1 := (3 / 10 : ℚ)) (a := (137299 / 10000 : ℚ)) (b := (137301 / 10000 : ℚ)) (r := (19 / 100 : ℚ)) (B := (937 / 125 : ℚ))
    (hs := (1 / 100 : ℚ)) (ht := (1 / 10000 : ℚ)) (h := (50003 / 5000000 : ℚ)) (u := (71897189 / 118750000 : ℚ)) (U := (1 : ℚ)) (R := (697 / 50 : ℚ)) (d := (135399 / 10000 : ℚ))
    (ns := 5) (nt := 1) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,3000; 0,6000] × [13,7299; 13,7301]`: 15×1 centros, r = 0,2900, B = 7,524, máx |ζ(c)| ≈ 0,368 ≤ u = 0,741. -/
theorem B3 : ∀ z ∈ ret (((3 / 10 : ℚ)) : ℝ) (((3 / 5 : ℚ)) : ℝ) (((137299 / 10000 : ℚ)) : ℝ) (((137301 / 10000 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (3 / 10 : ℚ)) (s1 := (3 / 5 : ℚ)) (a := (137299 / 10000 : ℚ)) (b := (137301 / 10000 : ℚ)) (r := (29 / 100 : ℚ)) (B := (1881 / 250 : ℚ))
    (hs := (1 / 100 : ℚ)) (ht := (1 / 10000 : ℚ)) (h := (50003 / 5000000 : ℚ)) (u := (268444357 / 362500000 : ℚ)) (U := (1 : ℚ)) (R := (703 / 50 : ℚ)) (d := (134399 / 10000 : ℚ))
    (ns := 15) (nt := 1) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,6000; 0,9000] × [13,7299; 13,7301]`: 6×1 centros, r = 0,4000, B = 7,559, máx |ζ(c)| ≈ 0,365 ≤ u = 0,528. -/
theorem B4 : ∀ z ∈ ret (((3 / 5 : ℚ)) : ℝ) (((9 / 10 : ℚ)) : ℝ) (((137299 / 10000 : ℚ)) : ℝ) (((137301 / 10000 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (3 / 5 : ℚ)) (s1 := (9 / 10 : ℚ)) (a := (137299 / 10000 : ℚ)) (b := (137301 / 10000 : ℚ)) (r := (2 / 5 : ℚ)) (B := (7559 / 1000 : ℚ))
    (hs := (1 / 40 : ℚ)) (ht := (1 / 10000 : ℚ)) (h := (250003 / 10000000 : ℚ)) (u := (2110227323 / 4000000000 : ℚ)) (U := (1 : ℚ)) (R := (71 / 5 : ℚ)) (d := (133299 / 10000 : ℚ))
    (ns := 6) (nt := 1) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

end ClayRiemannProof.CertifiedZeros.SquarePieces2
