import ClayRiemannProof.Main
import ClayRiemannProof.Zeta.Symmetry
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A função `ξ` inteira e o primeiro coeficiente de Li

* **`xi`**: `ξ(s) = ½ s(s − 1) π^{−s/2} Γ(s/2) ζ(s)`, escrita com a parte inteira `Λ₀` da Mathlib como
  `ξ(s) = s(s − 1)/2 · Λ₀(s) + ½` (a mesma definição do projeto zeta23, para compatibilidade futura). É inteira
  (`differentiable_xi`), satisfaz `ξ(1 − s) = ξ(s)` e `ξ(s̄) = conj ξ(s)`, vale `½` em `0` e em `1`, e
  **seus zeros são exatamente os zeros não triviais de ζ** (`xi_eq_zero_iff`). Daí, Clay ⟺ todo zero de `ξ` está na
  reta (`target_iff_xi`).
* **Esqueleto colado**: o enunciado `∀ ρ, riemannZeta ρ = 0 → ρ.re = 1/2` é **falso** (`esqueleto_falso`), porque
  `ζ(−2) = 0`. O enunciado correto exclui os zeros triviais e `s = 1` (é o `RiemannHypothesis` da Mathlib).
* **Coeficientes de Li pela definição por derivadas** (`li`): `λ_n = (1/(n − 1)!) dⁿ/dsⁿ [s^{n−1} log ξ(s)]` em
  `s = 1`, sem zeros e sem Hadamard. O primeiro coeficiente é calculado: `λ₁ = ξ'(1)/ξ(1) = Λ₀(1)` e
  `λ₁ = 1 + γ/2 − ½ log 4π` (`li_one_eq`); numericamente `0,004 < λ₁ < 0,09`, logo `λ₁ > 0` (`li_one_pos`). O
  valor verdadeiro é `0,0230957…`.
* **Enunciados corretos do que falta** (hipóteses nomeadas, nunca `axiom`): `HadamardXi` (produto de Hadamard de
  `ξ`, com `HasProd`, sem o valor-lixo de `∏'`) e `Li1997` (critério de Li com os `λ_n` acima).

Nada aqui prova RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Xi

open Complex ComplexConjugate ClayRiemannProof.Zeta.Symmetry

/-! ## 1. `ξ` inteira -/

/-- `ξ(s) = ½ s(s − 1) Λ(s)`, escrita com a parte inteira `Λ₀`. -/
noncomputable def xi (s : ℂ) : ℂ := s * (s - 1) / 2 * completedRiemannZeta₀ s + 1 / 2

theorem differentiable_xi : Differentiable ℂ xi := by
  unfold xi
  exact (((differentiable_id.mul (differentiable_id.sub_const 1)).div_const 2).mul
    differentiable_completedZeta₀).add_const _

/-- Fora de `0` e `1`, `ξ(s) = ½ s(s − 1) Λ(s)`. -/
theorem xi_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) : xi s = s * (s - 1) / 2 * completedRiemannZeta s := by
  unfold xi
  rw [completedRiemannZeta_eq]
  have h1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  ring

theorem xi_zero : xi 0 = 1 / 2 := by
  unfold xi
  ring

theorem xi_one : xi 1 = 1 / 2 := by
  unfold xi
  ring

/-- Equação funcional: `ξ(1 − s) = ξ(s)`. -/
theorem xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
  unfold xi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- Conjugação: `ξ(s̄) = conj ξ(s)`. -/
theorem xi_conj (s : ℂ) : xi (conj s) = conj (xi s) := by
  by_cases h0 : s = 0
  · subst h0
    rw [map_zero, xi_zero, map_div₀, map_one, map_ofNat]
  by_cases h1 : s = 1
  · subst h1
    rw [map_one, xi_one, map_div₀, map_one, map_ofNat]
  have h0' : conj s ≠ 0 := by simpa using h0
  have h1' : conj s ≠ 1 := by
    intro h
    apply h1
    simpa using congrArg conj h
  rw [xi_eq h0' h1', xi_eq h0 h1, completedRiemannZeta_conj]
  simp [map_mul, map_div₀, map_sub, map_one, map_ofNat]

/-- Na faixa `Re s > 0`, `Λ(s) = 0 ⟺ ζ(s) = 0`. -/
theorem completed_eq_zero_iff {s : ℂ} (h : 0 < s.re) :
    completedRiemannZeta s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs, zero_re] at h
    exact lt_irrefl 0 h
  rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff]
  constructor
  · intro h'
    exact Or.inl h'
  · rintro (h' | h')
    · exact h'
    · exact absurd h' (Gammaℝ_ne_zero_of_re_pos h)

theorem xi_ne_zero_of_one_le_re {s : ℂ} (h : 1 ≤ s.re) : xi s ≠ 0 := by
  by_cases h1 : s = 1
  · rw [h1, xi_one]
    norm_num
  have h0 : s ≠ 0 := by
    intro hs
    rw [hs, zero_re] at h
    linarith
  rw [xi_eq h0 h1]
  have hz : completedRiemannZeta s ≠ 0 := fun hc =>
    riemannZeta_ne_zero_of_one_le_re h ((completed_eq_zero_iff (by linarith)).mp hc)
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  exact mul_ne_zero (div_ne_zero (mul_ne_zero h0 hs1) two_ne_zero) hz

/-- **Os zeros de `ξ` são exatamente os zeros não triviais de ζ.** -/
theorem xi_eq_zero_iff (s : ℂ) : xi s = 0 ↔ s ∈ Z := by
  constructor
  · intro hx
    have hlt : s.re < 1 := by
      by_contra h
      exact xi_ne_zero_of_one_le_re (not_lt.mp h) hx
    have hgt : 0 < s.re := by
      by_contra h
      have : 1 ≤ (1 - s).re := by
        rw [sub_re, one_re]
        linarith [not_lt.mp h]
      exact xi_ne_zero_of_one_le_re this (by rw [xi_one_sub]; exact hx)
    have h0 : s ≠ 0 := by
      intro hs
      rw [hs, zero_re] at hgt
      exact lt_irrefl 0 hgt
    have h1 : s ≠ 1 := by
      intro hs
      rw [hs, one_re] at hlt
      exact lt_irrefl 1 hlt
    rw [xi_eq h0 h1] at hx
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
    have hc : completedRiemannZeta s = 0 := by
      rcases mul_eq_zero.mp hx with h | h
      · exact absurd h (div_ne_zero (mul_ne_zero h0 hs1) two_ne_zero)
      · exact h
    exact ⟨(completed_eq_zero_iff hgt).mp hc, hgt, hlt⟩
  · rintro ⟨hz, hgt, hlt⟩
    have h0 : s ≠ 0 := by
      intro hs
      rw [hs, zero_re] at hgt
      exact lt_irrefl 0 hgt
    have h1 : s ≠ 1 := by
      intro hs
      rw [hs, one_re] at hlt
      exact lt_irrefl 1 hlt
    rw [xi_eq h0 h1, (completed_eq_zero_iff hgt).mpr hz, mul_zero]

/-- **Clay ⟺ todo zero de `ξ` está na reta.** -/
theorem target_iff_xi : Target ↔ ∀ s : ℂ, xi s = 0 → s.re = 1 / 2 := by
  constructor
  · intro hT s hs
    exact riemann_imp_re hT ((xi_eq_zero_iff s).mp hs)
  · intro h
    exact riemann_iff_torcao.mpr fun s hs => (torcao_fixo_iff s).mpr (h s ((xi_eq_zero_iff s).mpr hs))

/-- **O enunciado do esqueleto colado é falso**: sem excluir os zeros triviais, `ζ(−2) = 0` e `Re(−2) ≠ ½`. -/
theorem esqueleto_falso : ¬ ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 := by
  intro h
  have h2 := h (-2) (by simpa using riemannZeta_neg_two_mul_nat_add_one 0)
  norm_num at h2

/-! ## 2. Os coeficientes de Li pela definição por derivadas -/

/-- **Coeficientes de Li** (definição de Li, 1997): `λ_n = (1/(n − 1)!) dⁿ/dsⁿ [s^{n−1} log ξ(s)]` em `s = 1`. -/
noncomputable def li (n : ℕ) : ℂ :=
  (1 / ((n - 1).factorial : ℂ)) * iteratedDeriv n (fun s => s ^ (n - 1) * Complex.log (xi s)) 1

/-- `ξ'(1) = Λ₀(1)/2`. -/
theorem hasDerivAt_xi_one : HasDerivAt xi (completedRiemannZeta₀ 1 / 2) 1 := by
  have hΛ := (differentiable_completedZeta₀ 1).hasDerivAt
  have hf : HasDerivAt (fun s : ℂ => s * (s - 1) / 2) ((1 * (1 - 1) + 1 * 1) / 2) 1 :=
    ((hasDerivAt_id (1 : ℂ)).mul ((hasDerivAt_id (1 : ℂ)).sub_const 1)).div_const 2
  have := (hf.mul hΛ).add_const (1 / 2 : ℂ)
  unfold xi
  convert this using 1
  ring

/-- **`λ₁ = ξ'(1)/ξ(1) = Λ₀(1)`.** -/
theorem li_one_eq_logDeriv : li 1 = logDeriv xi 1 := by
  have hslit : xi 1 ∈ slitPlane := by
    rw [xi_one]
    exact Or.inl (by norm_num)
  have hlog := (differentiable_xi 1).hasDerivAt.clog hslit
  unfold li
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, div_one, pow_zero, one_mul,
    iteratedDeriv_one]
  rw [hlog.deriv, logDeriv_apply]

theorem li_one_eq_completed : li 1 = completedRiemannZeta₀ 1 := by
  rw [li_one_eq_logDeriv, logDeriv_apply, hasDerivAt_xi_one.deriv, xi_one]
  field_simp

/-- **`λ₁ = 1 + γ/2 − ½ log 4π`** (valor exato; `γ` é a constante de Euler–Mascheroni). -/
theorem li_one_eq :
    li 1 = (((Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1 : ℝ) : ℂ) := by
  rw [li_one_eq_completed, completedRiemannZeta₀_one]
  have h4 : (4 : ℂ) * (Real.pi : ℂ) = ((4 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [h4, ← Complex.ofReal_log (by positivity)]
  push_cast
  ring

/-- `γ > 0,5456` (sequência de Euler–Mascheroni em `n = 15`). -/
theorem gamma_gt : (0.5456 : ℝ) < Real.eulerMascheroniConstant := by
  refine lt_trans ?_ (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 15)
  unfold Real.eulerMascheroniSeq
  have hlog : Real.log ((15 : ℕ) + 1 : ℝ) = 4 * Real.log 2 := by
    rw [show ((15 : ℕ) + 1 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  rw [hlog]
  have h2 := Real.log_two_lt_d9
  have hH : (harmonic 15 : ℝ) = 1195757 / 360360 := by
    simp [harmonic, Finset.sum_range_succ]
    norm_num
  rw [hH]
  linarith

/-- `log 4π < 2,5363`. -/
theorem log_four_pi_lt : Real.log (4 * Real.pi) < 2.5363 := by
  have hpi := Real.pi_lt_d4
  have hpos := Real.pi_pos
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h2 := Real.log_two_lt_d9
  have hexp : (3.1416 : ℝ) < Real.exp 1.15 := by
    rw [show (1.15 : ℝ) = 1 + 0.15 by norm_num, Real.exp_add]
    have he := Real.exp_one_gt_d9
    have hq := Real.quadratic_le_exp_of_nonneg (x := (0.15 : ℝ)) (by norm_num)
    nlinarith [Real.exp_pos 1]
  have hlogpi : Real.log Real.pi < 1.15 := by
    rw [Real.log_lt_iff_lt_exp hpos]
    linarith
  rw [Real.log_mul (by norm_num) hpos.ne', hlog4]
  linarith

/-- `log 4π > 2,5`. -/
theorem log_four_pi_gt : (2.5 : ℝ) < Real.log (4 * Real.pi) := by
  have hpi := Real.pi_gt_d2
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  have he := Real.exp_one_lt_d9
  have hhalf : Real.exp 0.5 < 1.65 := by
    have hsq : Real.exp 0.5 ^ 2 = Real.exp 1 := by
      rw [← Real.exp_nat_mul]
      norm_num
    nlinarith [Real.exp_pos 0.5]
  have h25 : Real.exp 2.5 = Real.exp 1 * Real.exp 1 * Real.exp 0.5 := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  rw [h25]
  have h1 : Real.exp 1 * Real.exp 1 < 2.7182818286 * 2.7182818286 := by
    nlinarith [Real.exp_pos 1]
  nlinarith [Real.exp_pos 1, Real.exp_pos 0.5, mul_pos (Real.exp_pos 1) (Real.exp_pos 1)]

/-- **`0,004 < λ₁ < 0,09`**: o primeiro coeficiente de Li é positivo. -/
theorem li_one_bounds :
    (0.004 : ℝ) < (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1 ∧
      (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1 < 0.09 := by
  have hg := gamma_gt
  have hg' := Real.eulerMascheroniConstant_lt_two_thirds
  have hl := log_four_pi_lt
  have hl' := log_four_pi_gt
  constructor <;> linarith

/-- **`λ₁` é real e positivo.** -/
theorem li_one_pos : (li 1).im = 0 ∧ 0 < (li 1).re := by
  rw [li_one_eq, ofReal_im, ofReal_re]
  exact ⟨rfl, lt_trans (by norm_num) li_one_bounds.1⟩

/-! ## 3. Enunciados corretos do que falta (hipóteses nomeadas, não provadas) -/

/-- **Produto de Hadamard de `ξ`** (não provado aqui): existem `A, B` e uma enumeração `ρ` dos zeros de `ξ` com
`ξ(s) = e^{A + Bs} ∏ (1 − s/ρₙ) e^{s/ρₙ}`, com o produto como `HasProd` (convergência de verdade, não o valor-lixo
`1` que `∏'` devolve quando o produto não converge). -/
def HadamardXi : Prop :=
  ∃ (A B : ℂ) (ρ : ℕ → ℂ), (∀ s, xi s = 0 ↔ ∃ n, ρ n = s) ∧
    ∀ s, HasProd (fun n => (1 - s / ρ n) * cexp (s / ρ n)) (xi s / cexp (A + B * s))

/-- **Critério de Li** (X.-J. Li, 1997), com os `λ_n` definidos por derivadas: resultado externo, hipótese nomeada. -/
def Li1997 : Prop := Target ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ (li n).re

end ClayRiemannProof.Xi
