import ClayRiemannProof.CertifiedZeros.FirstZero
import ClayRiemannProof.CertifiedZeros.SquarePieces1
import ClayRiemannProof.CertifiedZeros.SquarePieces2
import ClayRiemannProof.CertifiedZeros.SquarePieces3

/-!
# A bola de unicidade do primeiro zero, alargada: as cotas do quadrado no lugar de 240

`FirstZero.lean` usa `‖ζ‖ ≤ 240` no disco `|s − z₀| ≤ 2/5` (Euler–Maclaurin de ordem 1); daí, por Cauchy,
`‖ζ″‖ ≤ 240/0,19² ≈ 6 648`, e a contração `g(z) = z − ζ(z)/c` só fecha numa bola de raio `10⁻⁶`. Aqui a mesma
contração é refeita com a cota como parâmetro (`zero_na_bola_geral`), e com duas cotas melhores:

* **`cota_disco_cotaQ`**: a cota grosseira geral do kernel (`CrudeBound.cotaQ`, `N = 6`, `M = 10`) no quadrado
  `[1/10, 9/10] × [1373/100, 727/50]`, que contém o disco, dá `‖ζ‖ ≤ 7,64` sem avaliação nova: **bola de raio
  `1/500`** (`zero_na_bola_cotaQ`);
* **`cota_quadrado`**: `‖ζ‖ ≤ 1` no quadrado inteiro. As quatro arestas são certificadas por 26 peças
  (`SquarePieces1`–`3`, 150 avaliações de `ζ` pelo kernel, `UpperBound.peca_sup`), e o princípio do máximo
  (`UpperBound.maximo_ret`) leva a cota do bordo para dentro: **bola de raio `9/625 = 0,0144`**
  (`zero_na_bola_quadrado`), 14 400 vezes a de `FirstZero`.

Em cada bola há um único zero `ρ₁`, com `Re ρ₁ = ½` exato (simetria `s ↦ 1 − s̄`), simples (`ζ′ ≠ 0` na bola
inteira). E `circulo_de_Li`: `w = 1 − 1/s` leva a reta no círculo unitário, logo `|1 − 1/ρ₁| = 1`.

O círculo `|s − z₀| = 2/5` daria cota menor (`max |ζ| ≈ 0,376` contra `0,548` no quadrado, em ponto flutuante,
`computations/contorno/`), mas o bordo do quadrado é feito de arestas retas, que `ret` cobre; o círculo pediria
cobrir uma curva. **O que isto não é**: não é RH; é um zero. Não diz que `ρ₁` é o zero mais baixo (falta cobrir
`13 ≤ Im s ≤ Im ρ₁` fora da bola). `OPEN_MATH = true`. Arquivo novo (não vem do ATK).
-/

open Complex Metric Set

namespace ClayRiemannProof.CertifiedZeros.LargerBall

open ClayRiemannProof.Cert.Interval ClayRiemannProof.EulerMaclaurin.General
  ClayRiemannProof.CertifiedZeros.EulerMaclaurinData ClayRiemannProof.CertifiedZeros.CrudeBound
  ClayRiemannProof.CertifiedZeros.Evaluation ClayRiemannProof.CertifiedZeros.Rectangle
  ClayRiemannProof.CertifiedZeros.UpperBound ClayRiemannProof.CertifiedZeros.FirstZero
  ClayRiemannProof.Zeta.Symmetry

/-! ## 1. Dois números do certificado, conferidos de novo pelo kernel -/

set_option maxRecDepth 100000 in
/-- `Re c ≥ 0,78329` (`c` é o quociente de diferenças de `FirstZero`). -/
theorem cQ1_ge : (78329 / 100000 : ℚ) ≤ cQ.1 := by decide +kernel

set_option maxRecDepth 100000 in
/-- Os raios (ℓ¹) dos dois retângulos certificados somam `≤ 2,3·10⁻⁸`. -/
theorem radC_soma_le : radC J0 + radC J1 ≤ 23 / 10 ^ 9 := by decide +kernel

/-! ## 2. O quadrado -/

theorem disco_no_quadrado {w : ℂ} (hw : w ∈ closedBall z0 (2 / 5)) :
    w ∈ ret ((1 / 10 : ℚ) : ℝ) ((9 / 10 : ℚ) : ℝ) ((1373 / 100 : ℚ) : ℝ) ((727 / 50 : ℚ) : ℝ) := by
  obtain ⟨hre, him⟩ := re_im_prox hw
  rw [t0_val] at him
  rw [abs_le] at hre him
  obtain ⟨a1, a2⟩ := hre
  obtain ⟨b1, b2⟩ := him
  norm_num at a1 a2 b1 b2 ⊢
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- **`‖ζ‖ ≤ 7,64` no disco**, pela cota grosseira geral do kernel (sem avaliação nova). -/
theorem cota_disco_cotaQ {w : ℂ} (hw : w ∈ closedBall z0 (2 / 5)) :
    ‖riemannZeta w‖ ≤ ((191 / 25 : ℚ) : ℝ) := by
  obtain ⟨h1, h2, h3, h4⟩ := disco_no_quadrado hw
  obtain ⟨p0, p1, p2, p3⟩ := reg_ret (s0 := ((1 / 10 : ℚ) : ℝ)) (s1 := ((9 / 10 : ℚ) : ℝ))
    (a := ((1373 / 100 : ℚ) : ℝ)) (b := ((727 / 50 : ℚ) : ℝ)) (r := 0) (R := ((1457 / 100 : ℚ) : ℝ))
    (d := ((1373 / 100 : ℚ) : ℝ)) (w := w) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by linarith) (by linarith) (by linarith) (by linarith)
  have hc := cota_geral (N := 6) (M := 10) (by norm_num) (by norm_num) p0 p1 p2 (by norm_num) p3
  rw [← cotaQ_spec (by norm_num)] at hc
  have hq : cotaQ 6 10 (1457 / 100) (1373 / 100) ≤ 191 / 25 := by decide +kernel
  exact hc.trans (by exact_mod_cast hq)

theorem aresta_esquerda : ∀ z ∈ ret ((999 / 10000 : ℚ) : ℝ) ((1001 / 10000 : ℚ) : ℝ) ((1373 / 100 : ℚ) : ℝ)
    ((727 / 50 : ℚ) : ℝ), ‖riemannZeta z‖ ≤ ((1 : ℚ) : ℝ) :=
  ret_split_im (tm := ((1383 / 100 : ℚ) : ℝ)) SquarePieces1.E1
    (ret_split_im (tm := ((1393 / 100 : ℚ) : ℝ)) SquarePieces1.E2
    (ret_split_im (tm := ((1403 / 100 : ℚ) : ℝ)) SquarePieces1.E3
    (ret_split_im (tm := ((1413 / 100 : ℚ) : ℝ)) SquarePieces1.E4
    (ret_split_im (tm := ((1423 / 100 : ℚ) : ℝ)) SquarePieces1.E5
    (ret_split_im (tm := ((1433 / 100 : ℚ) : ℝ)) SquarePieces1.E6
    (ret_split_im (tm := ((1443 / 100 : ℚ) : ℝ)) SquarePieces1.E7
    (ret_split_im (tm := ((1453 / 100 : ℚ) : ℝ)) SquarePieces1.E8
    (SquarePieces1.E9))))))))

theorem aresta_direita : ∀ z ∈ ret ((8999 / 10000 : ℚ) : ℝ) ((9001 / 10000 : ℚ) : ℝ) ((1373 / 100 : ℚ) : ℝ)
    ((727 / 50 : ℚ) : ℝ), ‖riemannZeta z‖ ≤ ((1 : ℚ) : ℝ) :=
  ret_split_im (tm := ((1383 / 100 : ℚ) : ℝ)) SquarePieces1.D1
    (ret_split_im (tm := ((1393 / 100 : ℚ) : ℝ)) SquarePieces1.D2
    (ret_split_im (tm := ((1403 / 100 : ℚ) : ℝ)) SquarePieces1.D3
    (ret_split_im (tm := ((1413 / 100 : ℚ) : ℝ)) SquarePieces1.D4
    (ret_split_im (tm := ((1423 / 100 : ℚ) : ℝ)) SquarePieces1.D5
    (ret_split_im (tm := ((1433 / 100 : ℚ) : ℝ)) SquarePieces1.D6
    (ret_split_im (tm := ((1443 / 100 : ℚ) : ℝ)) SquarePieces1.D7
    (ret_split_im (tm := ((1453 / 100 : ℚ) : ℝ)) SquarePieces1.D8
    (SquarePieces1.D9))))))))

theorem aresta_baixo : ∀ z ∈ ret ((1 / 10 : ℚ) : ℝ) ((9 / 10 : ℚ) : ℝ) ((137299 / 10000 : ℚ) : ℝ)
    ((137301 / 10000 : ℚ) : ℝ), ‖riemannZeta z‖ ≤ ((1 : ℚ) : ℝ) :=
  ret_split_re (sm := ((1 / 5 : ℚ) : ℝ)) SquarePieces2.B1
    (ret_split_re (sm := ((3 / 10 : ℚ) : ℝ)) SquarePieces2.B2
    (ret_split_re (sm := ((3 / 5 : ℚ) : ℝ)) SquarePieces2.B3
    (SquarePieces2.B4)))

theorem aresta_cima : ∀ z ∈ ret ((1 / 10 : ℚ) : ℝ) ((9 / 10 : ℚ) : ℝ) ((145399 / 10000 : ℚ) : ℝ)
    ((145401 / 10000 : ℚ) : ℝ), ‖riemannZeta z‖ ≤ ((1 : ℚ) : ℝ) :=
  ret_split_re (sm := ((1 / 5 : ℚ) : ℝ)) SquarePieces3.C1
    (ret_split_re (sm := ((3 / 10 : ℚ) : ℝ)) SquarePieces3.C2
    (ret_split_re (sm := ((3 / 5 : ℚ) : ℝ)) SquarePieces3.C3
    (SquarePieces3.C4)))

/-- **`‖ζ‖ ≤ 1` no quadrado `[1/10, 9/10] × [1373/100, 727/50]`**: as quatro arestas (150 avaliações
certificadas) e o princípio do máximo. -/
theorem cota_quadrado : ∀ z ∈ ret ((1 / 10 : ℚ) : ℝ) ((9 / 10 : ℚ) : ℝ) ((1373 / 100 : ℚ) : ℝ)
    ((727 / 50 : ℚ) : ℝ), ‖riemannZeta z‖ ≤ ((1 : ℚ) : ℝ) := by
  refine maximo_ret (by norm_num) (by norm_num) (by norm_num) ?_
  intro z ⟨h1, h2, h3, h4⟩ hb
  rcases hb with e | e | e | e
  · exact aresta_esquerda z ⟨by rw [e]; norm_num, by rw [e]; norm_num, h3, h4⟩
  · exact aresta_direita z ⟨by rw [e]; norm_num, by rw [e]; norm_num, h3, h4⟩
  · exact aresta_baixo z ⟨h1, h2, by rw [e]; norm_num, by rw [e]; norm_num⟩
  · exact aresta_cima z ⟨h1, h2, by rw [e]; norm_num, by rw [e]; norm_num⟩

/-- **`‖ζ‖ ≤ 1` no disco `|s − z₀| ≤ 2/5`.** -/
theorem cota_disco_quadrado {w : ℂ} (hw : w ∈ closedBall z0 (2 / 5)) : ‖riemannZeta w‖ ≤ ((1 : ℚ) : ℝ) :=
  cota_quadrado w (disco_no_quadrado hw)

/-! ## 3. A contração com a cota como parâmetro -/

section Geral

variable {B r1 r2 R : ℝ}

/-- Cauchy: `‖ζ′‖ ≤ B/r₁` em `|w − z₀| ≤ 2/5 − r₁`. -/
theorem cota_deriv_geral (hB : ∀ w ∈ closedBall z0 (2 / 5), ‖riemannZeta w‖ ≤ B) (hr1 : 0 < r1)
    {w : ℂ} (hw : w ∈ closedBall z0 (2 / 5 - r1)) : ‖deriv riemannZeta w‖ ≤ B / r1 := by
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr1
  · apply FirstZero.difOn_zeta.diffContOnCl_ball
    intro x hx
    exact ne_um (closedBall_subset_closedBall (by linarith) (bola_sub hw hx))
  · intro x hx
    exact hB x (closedBall_subset_closedBall (by linarith) (bola_sub hw (sphere_subset_closedBall hx)))

/-- Cauchy de novo: `‖ζ″‖ ≤ B/(r₁r₂)` em `|z − z₀| ≤ 2/5 − r₁ − r₂`. -/
theorem cota_deriv2_geral (hB : ∀ w ∈ closedBall z0 (2 / 5), ‖riemannZeta w‖ ≤ B) (hr1 : 0 < r1)
    (hr2 : 0 < r2) {z : ℂ} (hz : z ∈ closedBall z0 (2 / 5 - r1 - r2)) :
    ‖deriv (deriv riemannZeta) z‖ ≤ B / r1 / r2 := by
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr2
  · apply FirstZero.difOn_dzeta.diffContOnCl_ball
    intro x hx
    exact ne_um (closedBall_subset_closedBall (by linarith) (bola_sub hz hx))
  · intro x hx
    exact cota_deriv_geral hB hr1
      (closedBall_subset_closedBall (by linarith) (bola_sub hz (sphere_subset_closedBall hx)))

theorem B_nonneg (hB : ∀ w ∈ closedBall z0 (2 / 5), ‖riemannZeta w‖ ≤ B) : 0 ≤ B :=
  (norm_nonneg _).trans (hB z0 (mem_closedBall_self (by norm_num)))

/-- `ζ′` é `B/(r₁r₂)`-Lipschitz em `|s − z₀| ≤ R`. -/
theorem lip_deriv_geral (hB : ∀ w ∈ closedBall z0 (2 / 5), ‖riemannZeta w‖ ≤ B) (hr1 : 0 < r1)
    (hr2 : 0 < r2) (hsum : R + r1 + r2 ≤ 2 / 5) {x y : ℂ} (hx : x ∈ closedBall z0 R)
    (hy : y ∈ closedBall z0 R) :
    ‖deriv riemannZeta y - deriv riemannZeta x‖ ≤ B / r1 / r2 * ‖y - x‖ :=
  (convex_closedBall z0 R).norm_image_sub_le_of_norm_deriv_le
    (fun u hu => dif_at' (closedBall_subset_closedBall (by linarith) hu))
    (fun u hu => cota_deriv2_geral hB hr1 hr2 (closedBall_subset_closedBall (by linarith) hu)) hx hy

theorem dq_le_geral (hB : ∀ w ∈ closedBall z0 (2 / 5), ‖riemannZeta w‖ ≤ B) (hr1 : 0 < r1)
    (hr2 : 0 < r2) (hsum : R + r1 + r2 ≤ 2 / 5) (hdl : ((dl : ℚ) : ℝ) ≤ R) :
    ‖riemannZeta z1 - riemannZeta z0 - (z1 - z0) * deriv riemannZeta z0‖ ≤
      B / r1 / r2 * ((dl : ℚ) : ℝ) * ‖z1 - z0‖ := by
  set c := deriv riemannZeta z0
  set φ : ℂ → ℂ := fun u => riemannZeta u - u * c with hφ
  have hd0 := dl_pos
  have hd : ∀ u ∈ closedBall z0 ((dl : ℚ) : ℝ), HasDerivAt φ (deriv riemannZeta u - c) u := by
    intro u hu
    have h1 := (dif_at (closedBall_subset_closedBall (by linarith) hu)).hasDerivAt
    have h2 := (hasDerivAt_id u).mul_const c
    have h3 : HasDerivAt (fun u => riemannZeta u - u * c) (deriv riemannZeta u - 1 * c) u :=
      h1.sub h2
    rw [one_mul] at h3
    exact h3
  have hF : 0 ≤ B / r1 / r2 := div_nonneg (div_nonneg (B_nonneg hB) hr1.le) hr2.le
  have hb : ∀ u ∈ closedBall z0 ((dl : ℚ) : ℝ), ‖deriv φ u‖ ≤ B / r1 / r2 * ((dl : ℚ) : ℝ) := by
    intro u hu
    rw [(hd u hu).deriv]
    have hu' : u ∈ closedBall z0 R := closedBall_subset_closedBall hdl hu
    have hz0 : z0 ∈ closedBall z0 R := mem_closedBall_self (by linarith)
    have := lip_deriv_geral hB hr1 hr2 hsum hz0 hu'
    rw [mem_closedBall, dist_eq_norm] at hu
    calc ‖deriv riemannZeta u - c‖ ≤ B / r1 / r2 * ‖u - z0‖ := this
      _ ≤ B / r1 / r2 * ((dl : ℚ) : ℝ) := mul_le_mul_of_nonneg_left hu hF
  have hm := (convex_closedBall z0 ((dl : ℚ) : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun u hu => (hd u hu).differentiableAt) hb (mem_closedBall_self dl_pos.le) (z1_mem le_rfl)
  have e : φ z1 - φ z0 = riemannZeta z1 - riemannZeta z0 - (z1 - z0) * c := by
    simp only [hφ]; ring
  rw [e] at hm
  exact hm

/-- `|ζ′(z₀) − c| ≤ F₂δ + (r₀ + r₁)/δ` com `F₂ = B/(r₁r₂)`. -/
theorem deriv_menos_c_geral (hB : ∀ w ∈ closedBall z0 (2 / 5), ‖riemannZeta w‖ ≤ B) (hr1 : 0 < r1)
    (hr2 : 0 < r2) (hsum : R + r1 + r2 ≤ 2 / 5) (hdl : ((dl : ℚ) : ℝ) ≤ R) :
    ‖deriv riemannZeta z0 - cC‖ ≤
      B / r1 / r2 * ((dl : ℚ) : ℝ) + ((radC J0 : ℝ) + (radC J1 : ℝ)) / ((dl : ℚ) : ℝ) := by
  have hz : z1 - z0 ≠ 0 := by
    intro h; have := norm_z1_sub; rw [h, norm_zero] at this; linarith [dl_pos]
  have hn := norm_z1_sub
  have key : deriv riemannZeta z0 - cC =
      -((riemannZeta z1 - riemannZeta z0 - (z1 - z0) * deriv riemannZeta z0) / (z1 - z0)) +
        ((riemannZeta z1 - cenC J1) - (riemannZeta z0 - cenC J0)) / (z1 - z0) := by
    have := cC_mul
    field_simp
    linear_combination (-1 : ℂ) * this
  rw [key]
  refine (norm_add_le _ _).trans ?_
  rw [norm_neg, norm_div, norm_div, hn]
  have h1 : ‖riemannZeta z1 - riemannZeta z0 - (z1 - z0) * deriv riemannZeta z0‖ /
      ((dl : ℚ) : ℝ) ≤ B / r1 / r2 * ((dl : ℚ) : ℝ) := by
    rw [div_le_iff₀ dl_pos]
    have := dq_le_geral hB hr1 hr2 hsum hdl
    rw [hn] at this
    linarith
  have h2 : ‖(riemannZeta z1 - cenC J1) - (riemannZeta z0 - cenC J0)‖ ≤
      (radC J1 : ℝ) + (radC J0 : ℝ) :=
    (norm_sub_le _ _).trans (add_le_add (norm_sub_cenC mem_J1) (norm_sub_cenC mem_J0))
  have h3 : ‖(riemannZeta z1 - cenC J1) - (riemannZeta z0 - cenC J0)‖ / ((dl : ℚ) : ℝ) ≤
      ((radC J0 : ℝ) + (radC J1 : ℝ)) / ((dl : ℚ) : ℝ) := by
    apply div_le_div_of_nonneg_right _ dl_pos.le
    linarith
  linarith

/-- A condição do certificado em números: `2,3·10⁻⁸/δ + F₂(δ + R) ≤ 0,78329/2`, `F₂ = B/(r₁r₂)`. -/
def CondicaoGeral (B r1 r2 R : ℝ) : Prop :=
  (23 / 10 ^ 9 : ℝ) / ((dl : ℚ) : ℝ) + B / r1 / r2 * (((dl : ℚ) : ℝ) + R) ≤ (78329 / 100000 : ℝ) / 2

theorem norm_deriv_g_geral (hB : ∀ w ∈ closedBall z0 (2 / 5), ‖riemannZeta w‖ ≤ B) (hr1 : 0 < r1)
    (hr2 : 0 < r2) (hsum : R + r1 + r2 ≤ 2 / 5) (hdl : ((dl : ℚ) : ℝ) ≤ R)
    (hc : CondicaoGeral B r1 r2 R) {z : ℂ} (hz : z ∈ closedBall z0 R) : ‖deriv g z‖ ≤ 1 / 2 := by
  have hz' : z ∈ closedBall z0 (2 / 5) := closedBall_subset_closedBall (by linarith) hz
  rw [(hasDerivAt_g hz').deriv]
  have hq1 : (78329 / 100000 : ℝ) ≤ ((cQ.1 : ℚ) : ℝ) := by
    have h' : ((78329 / 100000 : ℚ) : ℝ) ≤ ((cQ.1 : ℚ) : ℝ) := by exact_mod_cast cQ1_ge
    push_cast at h'
    exact h'
  have hrad : (radC J0 : ℝ) + (radC J1 : ℝ) ≤ 23 / 10 ^ 9 := by
    have h' : ((radC J0 + radC J1 : ℚ) : ℝ) ≤ ((23 / 10 ^ 9 : ℚ) : ℝ) := by exact_mod_cast radC_soma_le
    push_cast at h'
    exact h'
  have hrad' : ((radC J0 : ℝ) + (radC J1 : ℝ)) / ((dl : ℚ) : ℝ) ≤ (23 / 10 ^ 9 : ℝ) / ((dl : ℚ) : ℝ) :=
    div_le_div_of_nonneg_right hrad dl_pos.le
  have e : 1 - deriv riemannZeta z / cC = (cC - deriv riemannZeta z) / cC := by
    field_simp [cC_ne]
  rw [e, norm_div]
  have hcn := cC_norm_ge
  have hcpos : 0 < ‖cC‖ := lt_of_lt_of_le cQ1_pos hcn
  rw [div_le_iff₀ hcpos]
  have hz0 : z0 ∈ closedBall z0 R := mem_closedBall_self (le_trans dl_pos.le hdl)
  have hl := lip_deriv_geral hB hr1 hr2 hsum hz0 hz
  have hzr : ‖z - z0‖ ≤ R := by rwa [mem_closedBall, dist_eq_norm] at hz
  have hF : 0 ≤ B / r1 / r2 := div_nonneg (div_nonneg (B_nonneg hB) hr1.le) hr2.le
  have hdz := deriv_menos_c_geral hB hr1 hr2 hsum hdl
  have : ‖cC - deriv riemannZeta z‖ ≤
      ‖deriv riemannZeta z - deriv riemannZeta z0‖ + ‖deriv riemannZeta z0 - cC‖ := by
    rw [norm_sub_rev cC]
    exact norm_sub_le_norm_sub_add_norm_sub _ _ _
  have h4 : ‖deriv riemannZeta z - deriv riemannZeta z0‖ ≤ B / r1 / r2 * R :=
    hl.trans (mul_le_mul_of_nonneg_left hzr hF)
  unfold CondicaoGeral at hc
  nlinarith

theorem lip_g_geral (hB : ∀ w ∈ closedBall z0 (2 / 5), ‖riemannZeta w‖ ≤ B) (hr1 : 0 < r1)
    (hr2 : 0 < r2) (hsum : R + r1 + r2 ≤ 2 / 5) (hdl : ((dl : ℚ) : ℝ) ≤ R)
    (hc : CondicaoGeral B r1 r2 R) : LipschitzOnWith (1 / 2) g (closedBall z0 R) := by
  apply (convex_closedBall _ _).lipschitzOnWith_of_nnnorm_deriv_le
  · intro u hu
    exact (hasDerivAt_g (closedBall_subset_closedBall (by linarith) hu)).differentiableAt
  · intro u hu
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    have := norm_deriv_g_geral hB hr1 hr2 hsum hdl hc hu
    simpa using this

theorem g_maps_geral (hB : ∀ w ∈ closedBall z0 (2 / 5), ‖riemannZeta w‖ ≤ B) (hr1 : 0 < r1)
    (hr2 : 0 < r2) (hsum : R + r1 + r2 ≤ 2 / 5) (hdl : ((dl : ℚ) : ℝ) ≤ R)
    (hc : CondicaoGeral B r1 r2 R) (hrr : ((rr : ℚ) : ℝ) ≤ R) :
    MapsTo g (closedBall z0 R) (closedBall z0 R) := by
  intro z hz
  have hR0 : 0 ≤ R := le_trans dl_pos.le hdl
  have hz0 : z0 ∈ closedBall z0 R := mem_closedBall_self hR0
  have hl := (lip_g_geral hB hr1 hr2 hsum hdl hc).dist_le_mul z hz z0 hz0
  rw [mem_closedBall] at hz ⊢
  have h1 : dist (g z0) z0 ≤ R / 2 := by
    rw [dist_eq_norm]
    exact g_z0.trans (by linarith)
  calc dist (g z) z0 ≤ dist (g z) (g z0) + dist (g z0) z0 := dist_triangle _ _ _
    _ ≤ (1 / 2 : NNReal) * dist z z0 + R / 2 := add_le_add hl h1
    _ ≤ (1 / 2 : ℝ) * R + R / 2 := by push_cast; gcongr
    _ = R := by ring

/-- **A contração com a cota como parâmetro.** Se `‖ζ‖ ≤ B` no disco `|s − z₀| ≤ 2/5`, `R + r₁ + r₂ ≤ 2/5`,
`10⁻⁶ ≤ R` e a condição do certificado vale com `F₂ = B/(r₁r₂)`, então há um único zero `ρ` de `ζ` na bola
`|s − z₀| ≤ R`; ele é não trivial, está na reta (`Re ρ = ½` exato) e `ζ′` não se anula na bola. -/
theorem zero_na_bola_geral (hB : ∀ w ∈ closedBall z0 (2 / 5), ‖riemannZeta w‖ ≤ B) (hr1 : 0 < r1)
    (hr2 : 0 < r2) (hsum : R + r1 + r2 ≤ 2 / 5) (hrr : ((rr : ℚ) : ℝ) ≤ R) (hdl : ((dl : ℚ) : ℝ) ≤ R)
    (hc : CondicaoGeral B r1 r2 R) :
    ∃ ρ ∈ Z, ρ.re = 1 / 2 ∧ ρ ∈ closedBall z0 R ∧ (∀ w ∈ closedBall z0 R, riemannZeta w = 0 → w = ρ) ∧
      ∀ w ∈ closedBall z0 R, deriv riemannZeta w ≠ 0 := by
  set Bl := closedBall z0 R
  have hR0 : 0 ≤ R := le_trans dl_pos.le hdl
  have hz0 : z0 ∈ Bl := mem_closedBall_self hR0
  have hmaps := g_maps_geral hB hr1 hr2 hsum hdl hc hrr
  have hlip := lip_g_geral hB hr1 hr2 hsum hdl hc
  have hK : ContractingWith (1 / 2) (hmaps.restrict g Bl Bl) :=
    ⟨by rw [← NNReal.coe_lt_coe]; norm_num, hlip.mapsToRestrict hmaps⟩
  obtain ⟨y, hyB, hyfix, -⟩ := hK.exists_fixedPoint' isClosed_closedBall.isComplete hmaps hz0
    (edist_ne_top _ _)
  have hy0 : riemannZeta y = 0 := (fixo_iff y).mp hyfix
  have uniq : ∀ w ∈ Bl, riemannZeta w = 0 → w = y := by
    intro w hw hw0
    have hwf := (fixo_iff w).mpr hw0
    have hl := hlip.dist_le_mul w hw y hyB
    rw [hwf, show g y = y from hyfix] at hl
    have : dist w y = 0 := by
      have := dist_nonneg (x := w) (y := y)
      push_cast at hl
      linarith
    exact dist_eq_zero.mp this
  have hyZ : y ∈ Z := by
    obtain ⟨hre, -⟩ := re_im_prox hyB
    rw [abs_le] at hre
    exact ⟨hy0, by linarith [hre.1], by linarith [hre.2]⟩
  have htZ := torcao_mem_Z hyZ
  have ht : torcao y = y := uniq _ (torcao_bola hyB) htZ.1
  refine ⟨y, hyZ, (torcao_fixo_iff y).mp ht, hyB, uniq, fun w hw h0 => ?_⟩
  have hd := norm_deriv_g_geral hB hr1 hr2 hsum hdl hc hw
  rw [(hasDerivAt_g (closedBall_subset_closedBall (by linarith) hw)).deriv, h0, zero_div, sub_zero,
    norm_one] at hd
  norm_num at hd

end Geral

/-! ## 4. As duas bolas -/

/-- **Bola de raio `1/500`** (cota `cotaQ` = 7,64, sem avaliação nova; `F₂ = 7,64/0,199² ≈ 193`). -/
theorem zero_na_bola_cotaQ :
    ∃ ρ ∈ Z, ρ.re = 1 / 2 ∧ ρ ∈ closedBall z0 (1 / 500) ∧
      (∀ w ∈ closedBall z0 (1 / 500), riemannZeta w = 0 → w = ρ) ∧
      ∀ w ∈ closedBall z0 (1 / 500), deriv riemannZeta w ≠ 0 :=
  zero_na_bola_geral (B := ((191 / 25 : ℚ) : ℝ)) (r1 := 199 / 1000) (r2 := 199 / 1000)
    (fun w hw => cota_disco_cotaQ hw) (by norm_num) (by norm_num) (by norm_num)
    (by simp [FirstZero.rr]; norm_num) (by simp [dl]; norm_num)
    (by unfold CondicaoGeral; simp [dl]; norm_num)

/-- **Bola de raio `9/625 = 0,0144`** (cota do quadrado `1`; `F₂ = 1/0,1928² ≈ 26,9`). -/
theorem zero_na_bola_quadrado :
    ∃ ρ ∈ Z, ρ.re = 1 / 2 ∧ ρ ∈ closedBall z0 (9 / 625) ∧
      (∀ w ∈ closedBall z0 (9 / 625), riemannZeta w = 0 → w = ρ) ∧
      ∀ w ∈ closedBall z0 (9 / 625), deriv riemannZeta w ≠ 0 :=
  zero_na_bola_geral (B := ((1 : ℚ) : ℝ)) (r1 := 241 / 1250) (r2 := 241 / 1250)
    (fun w hw => cota_disco_quadrado hw) (by norm_num) (by norm_num) (by norm_num)
    (by simp [FirstZero.rr]; norm_num) (by simp [dl]; norm_num)
    (by unfold CondicaoGeral; simp [dl]; norm_num)

/-- **Nenhum outro zero a menos de `0,0144` de `z₀`**: o zero de `FirstZero.zero_na_linha` é o único zero de
`ζ` (trivial ou não) no disco `|s − z₀| ≤ 9/625`. -/
theorem unico_ate_0_0144 :
    ∃ ρ ∈ Z, ρ.re = 1 / 2 ∧ ρ ∈ closedBall z0 ((rr : ℚ) : ℝ) ∧
      ∀ w ∈ closedBall z0 (9 / 625), riemannZeta w = 0 → w = ρ := by
  obtain ⟨ρ, hρ, hre, -, hu, -⟩ := zero_na_bola_quadrado
  obtain ⟨ρ', hρ', -, hB', -⟩ := zero_na_linha
  have hr : ((rr : ℚ) : ℝ) ≤ 9 / 625 := by simp [FirstZero.rr]; norm_num
  have e : ρ' = ρ := hu ρ' (closedBall_subset_closedBall hr hB') hρ'.1
  exact ⟨ρ, hρ, hre, e ▸ hB', hu⟩

/-! ## 5. No círculo de Li -/

/-- Na reta, `|1 − 1/s| = 1`: `w = 1 − 1/s` leva a reta crítica no círculo unitário. -/
theorem circulo_de_Li {s : ℂ} (hs : s.re = 1 / 2) : ‖1 - 1 / s‖ = 1 := by
  have h0 : s ≠ 0 := by intro h; rw [h, zero_re] at hs; norm_num at hs
  have hn : ‖s‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have e : 1 - 1 / s = (s - 1) / s := by field_simp
  rw [e, norm_div, div_eq_one_iff_eq hn]
  have h1 : ‖s - 1‖ ^ 2 = ‖s‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply, sub_re, sub_im, one_re, one_im, hs]
    ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

/-- **`ρ₁` no círculo de Li**: o primeiro zero certificado vai no círculo unitário, `|1 − 1/ρ₁| = 1`. -/
theorem rho1_no_circulo_de_Li : ∃ ρ ∈ Z, ρ ∈ closedBall z0 ((rr : ℚ) : ℝ) ∧ ‖1 - 1 / ρ‖ = 1 := by
  obtain ⟨ρ, hρ, hre, hB, -⟩ := zero_na_linha
  exact ⟨ρ, hρ, hB, circulo_de_Li hre⟩

end ClayRiemannProof.CertifiedZeros.LargerBall
