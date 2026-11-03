import Mathlib

/-!
# A lei da colisão: onde um par de zeros sai da reta primeiro

de Bruijn (1950) deforma `H₀(z) = ξ(½ + iz/2)/8` pelo fluxo do calor reverso `∂ₜH = −∂²_z H`; a constante de
de Bruijn–Newman `Λ` é o menor `t` a partir do qual todos os zeros de `H_t` são reais, e RH ⟺ `Λ ≤ 0`
(Rodgers–Tao 2018: `Λ ≥ 0`). Andando para `t < 0`, os zeros reais se aproximam e **um par só sai da reta colidindo**:
dois zeros reais viram um zero duplo e depois um par conjugado.

O modelo exato de um par isolado é `H_t(z) = z² − a² − 2t` (zeros `±a` em `t = 0`, distância `Δ = 2|a|`):

* `calor_t`, `calor_z`: satisfaz `∂ₜH = −2 = −∂²_z H`;
* `zeros_reais_iff`: os dois zeros são reais exatamente para `t ≥ −a²/2`;
* `colisao`: com a distância `Δ`, o tempo de colisão é `−Δ²/8`;
* `mais_proximo_sai_depois`: quanto menor `Δ`, mais perto de `t = 0` o par sai da reta.

Para `ζ`, Csordas–Smith–Varga (1994) acrescentam os vizinhos: um par de Lehmer (`Δ²g < 4/5`) dá
`Λ ≥ λ = ((1 − (5/4)Δ²g)^{4/5} − 1)/(8g) = −Δ²/8 + O(Δ⁴g)`. O termo principal é exatamente o `−Δ²/8` daqui.
Por isso o lugar onde um zero fora da reta apareceria primeiro, se aparecesse, é o par de zeros mais próximo
(normalizado pela densidade local). Nada aqui prova ou refuta RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Colisao

open Complex

/-- Um par isolado sob o fluxo do calor de de Bruijn: `H_t(z) = z² − a² − 2t`. -/
def H2 (a t : ℝ) (z : ℂ) : ℂ := z ^ 2 - (a : ℂ) ^ 2 - 2 * (t : ℂ)

/-- `∂ₜ H_t(z) = −2`. -/
theorem calor_t (a : ℝ) (z : ℂ) (t : ℝ) : HasDerivAt (fun s : ℝ => H2 a s z) (-2) t := by
  have h : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => z ^ 2 - (a : ℂ) ^ 2 - 2 * (s : ℂ)) (0 - 2 * 1) t :=
    (hasDerivAt_const t (z ^ 2 - (a : ℂ) ^ 2)).sub (h.const_mul (2 : ℂ))
  exact h2.congr_deriv (by ring)

/-- `∂²_z H_t(z) = 2`, logo `∂ₜH = −∂²_z H`. -/
theorem calor_z (a t : ℝ) (z : ℂ) : deriv (deriv (fun w => H2 a t w)) z = 2 := by
  have h1 : deriv (fun w => H2 a t w) = fun w => 2 * w := by
    funext w
    have h : HasDerivAt (fun w : ℂ => w ^ 2 - (a : ℂ) ^ 2 - 2 * (t : ℂ)) ((2 : ℕ) * w ^ (2 - 1)) w :=
      ((hasDerivAt_pow 2 w).sub_const _).sub_const _
    exact (h.congr_deriv (by norm_num)).deriv
  rw [h1]
  exact (((hasDerivAt_id z).const_mul (2 : ℂ)).congr_deriv (by ring)).deriv

/-- **Lei da colisão**: os dois zeros de `H_t` são reais exatamente para `t ≥ −a²/2`. -/
theorem zeros_reais_iff (a t : ℝ) :
    (∀ z : ℂ, H2 a t z = 0 → z.im = 0) ↔ -(a ^ 2) / 2 ≤ t := by
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    set c : ℝ := -(a ^ 2 + 2 * t) with hc
    have hcpos : 0 < c := by rw [hc]; linarith
    have hsq : ((Real.sqrt c : ℝ) : ℂ) ^ 2 = (c : ℂ) := by
      rw [← ofReal_pow, Real.sq_sqrt hcpos.le]
    have hz : H2 a t (I * (Real.sqrt c : ℂ)) = 0 := by
      unfold H2
      have : (I * (Real.sqrt c : ℂ)) ^ 2 = -(c : ℂ) := by rw [mul_pow, hsq, I_sq]; ring
      rw [this, hc]; push_cast; ring
    have him := h _ hz
    simp only [mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul, zero_add] at him
    exact (Real.sqrt_pos.mpr hcpos).ne' him
  · intro ht z hz
    unfold H2 at hz
    have hre := congrArg Complex.re hz
    have him := congrArg Complex.im hz
    simp only [sq, sub_re, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, zero_re, zero_im] at hre him
    norm_num at hre him
    -- him: 2·Re z·Im z = 0 ; hre: Re z² − Im z² − a² − 2t = 0
    by_contra hy
    have hx : z.re = 0 := by
      rcases mul_eq_zero.mp (by linarith [him] : z.re * z.im = 0) with h | h
      · exact h
      · exact absurd h hy
    rw [hx] at hre
    have : 0 < z.im * z.im := mul_self_pos.mpr hy
    nlinarith [sq_nonneg a]

/-- Com a distância `Δ` entre os dois zeros, o tempo de colisão é `−Δ²/8`. -/
theorem colisao (Δ t : ℝ) : (∀ z : ℂ, H2 (Δ / 2) t z = 0 → z.im = 0) ↔ -(Δ ^ 2) / 8 ≤ t := by
  rw [zeros_reais_iff]
  constructor <;> intro h <;> nlinarith

/-- O par mais próximo é o último a ficar na reta: para `|Δ₁| < |Δ₂|`, `−Δ₂²/8 < −Δ₁²/8`. -/
theorem mais_proximo_sai_depois {Δ₁ Δ₂ : ℝ} (h : |Δ₁| < |Δ₂|) : -(Δ₂ ^ 2) / 8 < -(Δ₁ ^ 2) / 8 := by
  have := sq_lt_sq.mpr h
  linarith

/-- Em `t = 0` (a função de partida) os dois zeros estão na reta real, qualquer que seja a distância. -/
theorem na_reta_em_zero (a : ℝ) : ∀ z : ℂ, H2 a 0 z = 0 → z.im = 0 :=
  (zeros_reais_iff a 0).mpr (by nlinarith [sq_nonneg a])

end ClayRiemannProof.Colisao
