import ClayRiemannProof.CertifiedZeros.UpperBound

/-!
# Peças do bordo do quadrado, arquivo 1 de 3: arestas verticais Re = 1/10 e Re = 9/10

O quadrado é `[1/10, 9/10] × [1373/100, 727/50]`, que contém o disco `|s − z₀| ≤ 2/5` em volta de
`z₀ = ½ + 14,1347251417 i`. Cada peça é um retângulo fino em volta de um trecho de aresta, certificado por
`UpperBound.peca_sup`: `‖ζ(c)‖ + (B/r)h ≤ 1,0` em todos os centros (`chkS`, `decide +kernel`, sem
`native_decide`), com `B = cotaQ` na região de Cauchy. Gerado por `computations/contorno/gera_pecas_lean.py` a partir
de `planeja_quadrado.py`. Arquivo novo (não vem do ATK).
-/

open Complex

namespace ClayRiemannProof.CertifiedZeros.SquarePieces1

open ClayRiemannProof.CertifiedZeros.Rectangle ClayRiemannProof.CertifiedZeros.UpperBound

set_option maxRecDepth 100000 in
/-- `[0,0999; 0,1001] × [13,7300; 13,8300]`: 1×8 centros, r = 0,0989, B = 7,495, máx |ζ(c)| ≈ 0,507 ≤ u = 0,526. -/
theorem E1 : ∀ z ∈ ret (((999 / 10000 : ℚ)) : ℝ) (((1001 / 10000 : ℚ)) : ℝ) (((1373 / 100 : ℚ)) : ℝ) (((1383 / 100 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (999 / 10000 : ℚ)) (s1 := (1001 / 10000 : ℚ)) (a := (1373 / 100 : ℚ)) (b := (1383 / 100 : ℚ)) (r := (989 / 10000 : ℚ)) (B := (1499 / 200 : ℚ))
    (hs := (1 / 10000 : ℚ)) (ht := (1 / 160 : ℚ)) (h := (62509 / 10000000 : ℚ)) (u := (104099009 / 197800000 : ℚ)) (U := (1 : ℚ)) (R := (279 / 20 : ℚ)) (d := (136311 / 10000 : ℚ))
    (ns := 1) (nt := 8) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,0999; 0,1001] × [13,8300; 13,9300]`: 1×7 centros, r = 0,0989, B = 7,513, máx |ζ(c)| ≈ 0,453 ≤ u = 0,457. -/
theorem E2 : ∀ z ∈ ret (((999 / 10000 : ℚ)) : ℝ) (((1001 / 10000 : ℚ)) : ℝ) (((1383 / 100 : ℚ)) : ℝ) (((1393 / 100 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (999 / 10000 : ℚ)) (s1 := (1001 / 10000 : ℚ)) (a := (1383 / 100 : ℚ)) (b := (1393 / 100 : ℚ)) (r := (989 / 10000 : ℚ)) (B := (7513 / 1000 : ℚ))
    (hs := (1 / 10000 : ℚ)) (ht := (1 / 140 : ℚ)) (h := (71437 / 10000000 : ℚ)) (u := (452293819 / 989000000 : ℚ)) (U := (1 : ℚ)) (R := (281 / 20 : ℚ)) (d := (137311 / 10000 : ℚ))
    (ns := 1) (nt := 7) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,0999; 0,1001] × [13,9300; 14,0300]`: 1×7 centros, r = 0,0989, B = 7,531, máx |ζ(c)| ≈ 0,410 ≤ u = 0,456. -/
theorem E3 : ∀ z ∈ ret (((999 / 10000 : ℚ)) : ℝ) (((1001 / 10000 : ℚ)) : ℝ) (((1393 / 100 : ℚ)) : ℝ) (((1403 / 100 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (999 / 10000 : ℚ)) (s1 := (1001 / 10000 : ℚ)) (a := (1393 / 100 : ℚ)) (b := (1403 / 100 : ℚ)) (r := (989 / 10000 : ℚ)) (B := (7531 / 1000 : ℚ))
    (hs := (1 / 10000 : ℚ)) (ht := (1 / 140 : ℚ)) (h := (71437 / 10000000 : ℚ)) (u := (451007953 / 989000000 : ℚ)) (U := (1 : ℚ)) (R := (283 / 20 : ℚ)) (d := (138311 / 10000 : ℚ))
    (ns := 1) (nt := 7) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,0999; 0,1001] × [14,0300; 14,1300]`: 1×7 centros, r = 0,0989, B = 7,551, máx |ζ(c)| ≈ 0,382 ≤ u = 0,455. -/
theorem E4 : ∀ z ∈ ret (((999 / 10000 : ℚ)) : ℝ) (((1001 / 10000 : ℚ)) : ℝ) (((1403 / 100 : ℚ)) : ℝ) (((1413 / 100 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (999 / 10000 : ℚ)) (s1 := (1001 / 10000 : ℚ)) (a := (1403 / 100 : ℚ)) (b := (1413 / 100 : ℚ)) (r := (989 / 10000 : ℚ)) (B := (7551 / 1000 : ℚ))
    (hs := (1 / 10000 : ℚ)) (ht := (1 / 140 : ℚ)) (h := (71437 / 10000000 : ℚ)) (u := (449579213 / 989000000 : ℚ)) (U := (1 : ℚ)) (R := (57 / 4 : ℚ)) (d := (139311 / 10000 : ℚ))
    (ns := 1) (nt := 7) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,0999; 0,1001] × [14,1300; 14,2300]`: 1×7 centros, r = 0,0989, B = 7,572, máx |ζ(c)| ≈ 0,387 ≤ u = 0,453. -/
theorem E5 : ∀ z ∈ ret (((999 / 10000 : ℚ)) : ℝ) (((1001 / 10000 : ℚ)) : ℝ) (((1413 / 100 : ℚ)) : ℝ) (((1423 / 100 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (999 / 10000 : ℚ)) (s1 := (1001 / 10000 : ℚ)) (a := (1413 / 100 : ℚ)) (b := (1423 / 100 : ℚ)) (r := (989 / 10000 : ℚ)) (B := (1893 / 250 : ℚ))
    (hs := (1 / 10000 : ℚ)) (ht := (1 / 140 : ℚ)) (h := (71437 / 10000000 : ℚ)) (u := (112019759 / 247250000 : ℚ)) (U := (1 : ℚ)) (R := (287 / 20 : ℚ)) (d := (140311 / 10000 : ℚ))
    (ns := 1) (nt := 7) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,0999; 0,1001] × [14,2300; 14,3300]`: 1×7 centros, r = 0,0989, B = 7,594, máx |ζ(c)| ≈ 0,421 ≤ u = 0,451. -/
theorem E6 : ∀ z ∈ ret (((999 / 10000 : ℚ)) : ℝ) (((1001 / 10000 : ℚ)) : ℝ) (((1423 / 100 : ℚ)) : ℝ) (((1433 / 100 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (999 / 10000 : ℚ)) (s1 := (1001 / 10000 : ℚ)) (a := (1423 / 100 : ℚ)) (b := (1433 / 100 : ℚ)) (r := (989 / 10000 : ℚ)) (B := (3797 / 500 : ℚ))
    (hs := (1 / 10000 : ℚ)) (ht := (1 / 140 : ℚ)) (h := (71437 / 10000000 : ℚ)) (u := (223253711 / 494500000 : ℚ)) (U := (1 : ℚ)) (R := (289 / 20 : ℚ)) (d := (141311 / 10000 : ℚ))
    (ns := 1) (nt := 7) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,0999; 0,1001] × [14,3300; 14,4300]`: 1×8 centros, r = 0,0989, B = 7,617, máx |ζ(c)| ≈ 0,474 ≤ u = 0,519. -/
theorem E7 : ∀ z ∈ ret (((999 / 10000 : ℚ)) : ℝ) (((1001 / 10000 : ℚ)) : ℝ) (((1433 / 100 : ℚ)) : ℝ) (((1443 / 100 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (999 / 10000 : ℚ)) (s1 := (1001 / 10000 : ℚ)) (a := (1433 / 100 : ℚ)) (b := (1443 / 100 : ℚ)) (r := (989 / 10000 : ℚ)) (B := (7617 / 1000 : ℚ))
    (hs := (1 / 10000 : ℚ)) (ht := (1 / 160 : ℚ)) (h := (62509 / 10000000 : ℚ)) (u := (512868947 / 989000000 : ℚ)) (U := (1 : ℚ)) (R := (291 / 20 : ℚ)) (d := (142311 / 10000 : ℚ))
    (ns := 1) (nt := 8) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,0999; 0,1001] × [14,4300; 14,5300]`: 1×9 centros, r = 0,0989, B = 7,642, máx |ζ(c)| ≈ 0,541 ≤ u = 0,571. -/
theorem E8 : ∀ z ∈ ret (((999 / 10000 : ℚ)) : ℝ) (((1001 / 10000 : ℚ)) : ℝ) (((1443 / 100 : ℚ)) : ℝ) (((1453 / 100 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (999 / 10000 : ℚ)) (s1 := (1001 / 10000 : ℚ)) (a := (1443 / 100 : ℚ)) (b := (1453 / 100 : ℚ)) (r := (989 / 10000 : ℚ)) (B := (3821 / 500 : ℚ))
    (hs := (1 / 10000 : ℚ)) (ht := (1 / 180 : ℚ)) (h := (27783 / 5000000 : ℚ)) (u := (141091157 / 247250000 : ℚ)) (U := (1 : ℚ)) (R := (293 / 20 : ℚ)) (d := (143311 / 10000 : ℚ))
    (ns := 1) (nt := 9) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,0999; 0,1001] × [14,5300; 14,5400]`: 1×1 centros, r = 0,0989, B = 7,642, máx |ζ(c)| ≈ 0,549 ≤ u = 0,614. -/
theorem E9 : ∀ z ∈ ret (((999 / 10000 : ℚ)) : ℝ) (((1001 / 10000 : ℚ)) : ℝ) (((1453 / 100 : ℚ)) : ℝ) (((727 / 50 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (999 / 10000 : ℚ)) (s1 := (1001 / 10000 : ℚ)) (a := (1453 / 100 : ℚ)) (b := (727 / 50 : ℚ)) (r := (989 / 10000 : ℚ)) (B := (3821 / 500 : ℚ))
    (hs := (1 / 10000 : ℚ)) (ht := (1 / 200 : ℚ)) (h := (50011 / 10000000 : ℚ)) (u := (303407969 / 494500000 : ℚ)) (U := (1 : ℚ)) (R := (733 / 50 : ℚ)) (d := (144311 / 10000 : ℚ))
    (ns := 1) (nt := 1) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,8999; 0,9001] × [13,7300; 13,8300]`: 1×2 centros, r = 0,4000, B = 7,582, máx |ζ(c)| ≈ 0,363 ≤ u = 0,526. -/
theorem D1 : ∀ z ∈ ret (((8999 / 10000 : ℚ)) : ℝ) (((9001 / 10000 : ℚ)) : ℝ) (((1373 / 100 : ℚ)) : ℝ) (((1383 / 100 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (8999 / 10000 : ℚ)) (s1 := (9001 / 10000 : ℚ)) (a := (1373 / 100 : ℚ)) (b := (1383 / 100 : ℚ)) (r := (2 / 5 : ℚ)) (B := (3791 / 500 : ℚ))
    (hs := (1 / 10000 : ℚ)) (ht := (1 / 40 : ℚ)) (h := (250003 / 10000000 : ℚ)) (u := (1052238627 / 2000000000 : ℚ)) (U := (1 : ℚ)) (R := (143 / 10 : ℚ)) (d := (1333 / 100 : ℚ))
    (ns := 1) (nt := 2) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,8999; 0,9001] × [13,8300; 13,9300]`: 1×2 centros, r = 0,4000, B = 7,604, máx |ζ(c)| ≈ 0,324 ≤ u = 0,525. -/
theorem D2 : ∀ z ∈ ret (((8999 / 10000 : ℚ)) : ℝ) (((9001 / 10000 : ℚ)) : ℝ) (((1383 / 100 : ℚ)) : ℝ) (((1393 / 100 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (8999 / 10000 : ℚ)) (s1 := (9001 / 10000 : ℚ)) (a := (1383 / 100 : ℚ)) (b := (1393 / 100 : ℚ)) (r := (2 / 5 : ℚ)) (B := (1901 / 250 : ℚ))
    (hs := (1 / 10000 : ℚ)) (ht := (1 / 40 : ℚ)) (h := (250003 / 10000000 : ℚ)) (u := (524744297 / 1000000000 : ℚ)) (U := (1 : ℚ)) (R := (72 / 5 : ℚ)) (d := (1343 / 100 : ℚ))
    (ns := 1) (nt := 2) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,8999; 0,9001] × [13,9300; 14,0300]`: 1×2 centros, r = 0,4000, B = 7,626, máx |ζ(c)| ≈ 0,293 ≤ u = 0,523. -/
theorem D3 : ∀ z ∈ ret (((8999 / 10000 : ℚ)) : ℝ) (((9001 / 10000 : ℚ)) : ℝ) (((1393 / 100 : ℚ)) : ℝ) (((1403 / 100 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (8999 / 10000 : ℚ)) (s1 := (9001 / 10000 : ℚ)) (a := (1393 / 100 : ℚ)) (b := (1403 / 100 : ℚ)) (r := (2 / 5 : ℚ)) (B := (3813 / 500 : ℚ))
    (hs := (1 / 10000 : ℚ)) (ht := (1 / 40 : ℚ)) (h := (250003 / 10000000 : ℚ)) (u := (1046738561 / 2000000000 : ℚ)) (U := (1 : ℚ)) (R := (29 / 2 : ℚ)) (d := (1353 / 100 : ℚ))
    (ns := 1) (nt := 2) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,8999; 0,9001] × [14,0300; 14,1300]`: 1×2 centros, r = 0,4000, B = 7,650, máx |ζ(c)| ≈ 0,275 ≤ u = 0,522. -/
theorem D4 : ∀ z ∈ ret (((8999 / 10000 : ℚ)) : ℝ) (((9001 / 10000 : ℚ)) : ℝ) (((1403 / 100 : ℚ)) : ℝ) (((1413 / 100 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (8999 / 10000 : ℚ)) (s1 := (9001 / 10000 : ℚ)) (a := (1403 / 100 : ℚ)) (b := (1413 / 100 : ℚ)) (r := (2 / 5 : ℚ)) (B := (153 / 20 : ℚ))
    (hs := (1 / 10000 : ℚ)) (ht := (1 / 40 : ℚ)) (h := (250003 / 10000000 : ℚ)) (u := (41749541 / 80000000 : ℚ)) (U := (1 : ℚ)) (R := (73 / 5 : ℚ)) (d := (1363 / 100 : ℚ))
    (ns := 1) (nt := 2) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,8999; 0,9001] × [14,1300; 14,2300]`: 1×2 centros, r = 0,4000, B = 7,675, máx |ζ(c)| ≈ 0,276 ≤ u = 0,520. -/
theorem D5 : ∀ z ∈ ret (((8999 / 10000 : ℚ)) : ℝ) (((9001 / 10000 : ℚ)) : ℝ) (((1413 / 100 : ℚ)) : ℝ) (((1423 / 100 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (8999 / 10000 : ℚ)) (s1 := (9001 / 10000 : ℚ)) (a := (1413 / 100 : ℚ)) (b := (1423 / 100 : ℚ)) (r := (2 / 5 : ℚ)) (B := (307 / 40 : ℚ))
    (hs := (1 / 10000 : ℚ)) (ht := (1 / 40 : ℚ)) (h := (250003 / 10000000 : ℚ)) (u := (83249079 / 160000000 : ℚ)) (U := (1 : ℚ)) (R := (147 / 10 : ℚ)) (d := (1373 / 100 : ℚ))
    (ns := 1) (nt := 2) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,8999; 0,9001] × [14,2300; 14,3300]`: 1×2 centros, r = 0,4000, B = 7,701, máx |ζ(c)| ≈ 0,298 ≤ u = 0,519. -/
theorem D6 : ∀ z ∈ ret (((8999 / 10000 : ℚ)) : ℝ) (((9001 / 10000 : ℚ)) : ℝ) (((1423 / 100 : ℚ)) : ℝ) (((1433 / 100 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (8999 / 10000 : ℚ)) (s1 := (9001 / 10000 : ℚ)) (a := (1423 / 100 : ℚ)) (b := (1433 / 100 : ℚ)) (r := (2 / 5 : ℚ)) (B := (7701 / 1000 : ℚ))
    (hs := (1 / 10000 : ℚ)) (ht := (1 / 40 : ℚ)) (h := (250003 / 10000000 : ℚ)) (u := (2074726897 / 4000000000 : ℚ)) (U := (1 : ℚ)) (R := (74 / 5 : ℚ)) (d := (1383 / 100 : ℚ))
    (ns := 1) (nt := 2) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,8999; 0,9001] × [14,3300; 14,4300]`: 1×2 centros, r = 0,4000, B = 7,728, máx |ζ(c)| ≈ 0,333 ≤ u = 0,517. -/
theorem D7 : ∀ z ∈ ret (((8999 / 10000 : ℚ)) : ℝ) (((9001 / 10000 : ℚ)) : ℝ) (((1433 / 100 : ℚ)) : ℝ) (((1443 / 100 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (8999 / 10000 : ℚ)) (s1 := (9001 / 10000 : ℚ)) (a := (1433 / 100 : ℚ)) (b := (1443 / 100 : ℚ)) (r := (2 / 5 : ℚ)) (B := (966 / 125 : ℚ))
    (hs := (1 / 10000 : ℚ)) (ht := (1 / 40 : ℚ)) (h := (250003 / 10000000 : ℚ)) (u := (129248551 / 250000000 : ℚ)) (U := (1 : ℚ)) (R := (149 / 10 : ℚ)) (d := (1393 / 100 : ℚ))
    (ns := 1) (nt := 2) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,8999; 0,9001] × [14,4300; 14,5300]`: 1×2 centros, r = 0,4000, B = 7,757, máx |ζ(c)| ≈ 0,377 ≤ u = 0,515. -/
theorem D8 : ∀ z ∈ ret (((8999 / 10000 : ℚ)) : ℝ) (((9001 / 10000 : ℚ)) : ℝ) (((1443 / 100 : ℚ)) : ℝ) (((1453 / 100 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (8999 / 10000 : ℚ)) (s1 := (9001 / 10000 : ℚ)) (a := (1443 / 100 : ℚ)) (b := (1453 / 100 : ℚ)) (r := (2 / 5 : ℚ)) (B := (7757 / 1000 : ℚ))
    (hs := (1 / 10000 : ℚ)) (ht := (1 / 40 : ℚ)) (h := (250003 / 10000000 : ℚ)) (u := (2060726729 / 4000000000 : ℚ)) (U := (1 : ℚ)) (R := (15 : ℚ)) (d := (1403 / 100 : ℚ))
    (ns := 1) (nt := 2) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

set_option maxRecDepth 100000 in
/-- `[0,8999; 0,9001] × [14,5300; 14,5400]`: 1×1 centros, r = 0,4000, B = 7,758, máx |ζ(c)| ≈ 0,392 ≤ u = 0,903. -/
theorem D9 : ∀ z ∈ ret (((8999 / 10000 : ℚ)) : ℝ) (((9001 / 10000 : ℚ)) : ℝ) (((1453 / 100 : ℚ)) : ℝ) (((727 / 50 : ℚ)) : ℝ),
    ‖riemannZeta z‖ ≤ (((1 : ℚ)) : ℝ) :=
  peca_sup (s0 := (8999 / 10000 : ℚ)) (s1 := (9001 / 10000 : ℚ)) (a := (1453 / 100 : ℚ)) (b := (727 / 50 : ℚ)) (r := (2 / 5 : ℚ)) (B := (3879 / 500 : ℚ))
    (hs := (1 / 10000 : ℚ)) (ht := (1 / 200 : ℚ)) (h := (50011 / 10000000 : ℚ)) (u := (1806007331 / 2000000000 : ℚ)) (U := (1 : ℚ)) (R := (1501 / 100 : ℚ)) (d := (1413 / 100 : ℚ))
    (ns := 1) (nt := 1) (Nc := 6) (Mc := 10) (Ne := 12) (Me := 8) (K := 16) (nT := 24) (p := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by decide +kernel)

end ClayRiemannProof.CertifiedZeros.SquarePieces1
