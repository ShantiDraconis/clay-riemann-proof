import ClayRiemannProof.Main
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# RH condicional ao "quasi-RH 1/8–7/8" (resultado externo)

`OpenAIQuasiRH78` é um **resultado externo**, enunciado aqui como `Prop` nomeada (não é axioma e não
é provado neste repositório). Com ele como hipótese:

* `target_iff_noZero_half_78`: `Target ↔ NoZero_half_78` — basta excluir zeros não triviais com
  `1/2 < Re s ≤ 7/8`.

Incondicional:

* `target_iff_noZero_right_half`: `Target ↔` "nenhum zero não trivial com `Re s > 1/2`"
  (equação funcional da Mathlib: um zero não trivial `s` com `0 < Re s < 1/2` dá o zero `1 − s`);
* `openAIQuasiRH78_of_target`: `Target → OpenAIQuasiRH78` (a hipótese não é trivialmente falsa:
  é consequência de RH).

Nada aqui prova RH: o que falta, sob a hipótese externa, é `NoZero_half_78`. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof

/-- **Quasi-hipótese de Riemann com faixa `[1/8, 7/8]`** (resultado externo, NÃO provado aqui):
todo zero não trivial de `ζ` tem `1/8 ≤ Re s ≤ 7/8`.

Fonte: OpenAI (autoria atribuída a "everyone at OpenAI"), versão verificada em Lean datada de
2026-09-30, anunciada em 2026-10-06; reportagem da Quanta Magazine de 2026-10-19:
https://quantamagazine.org/ai-proved-the-quasi-riemann-hypothesis-what-happens-now-20261019
(segundo a reportagem, uma versão posterior, de 2026-10-05, afirma só `1/12 ≤ Re s ≤ 11/12` e não
foi verificada em Lean). A formalização da OpenAI não foi conferida por este repositório; a
proposição entra apenas como hipótese nomeada. Os zeros não triviais são excluídos exatamente
como em `RiemannHypothesis` da Mathlib. -/
def OpenAIQuasiRH78 : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬ ∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
    1 / 8 ≤ s.re ∧ s.re ≤ 7 / 8

/-- Nenhum zero não trivial com `1/2 < Re s ≤ 7/8`. -/
def NoZero_half_78 : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬ ∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
    ¬ (1 / 2 < s.re ∧ s.re ≤ 7 / 8)

/-- Nenhum zero não trivial com `Re s > 1/2`. -/
def NoZero_right_half : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬ ∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → ¬ (1 / 2 < s.re)

/-- Um ponto de parte real positiva não é zero trivial. -/
theorem not_trivial_of_re_pos {s : ℂ} (h : 0 < s.re) : ¬ ∃ n : ℕ, s = -2 * (n + 1) := by
  rintro ⟨n, rfl⟩
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  simp at h
  linarith

/-- **Simetria dos zeros** (equação funcional da Mathlib): se `ζ(s) = 0` com `0 < Re s < 1`,
então `ζ(1 − s) = 0`. -/
theorem riemannZeta_one_sub_eq_zero {s : ℂ} (hz : riemannZeta s = 0) (h0 : 0 < s.re)
    (h1 : s.re < 1) : riemannZeta (1 - s) = 0 := by
  have hn : ∀ n : ℕ, s ≠ -n := by
    intro n hn
    have := congrArg Complex.re hn
    rw [Complex.neg_re, Complex.natCast_re] at this
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs1 : s ≠ 1 := by
    intro h; rw [h, Complex.one_re] at h1; exact lt_irrefl _ h1
  rw [riemannZeta_one_sub hn hs1, hz, mul_zero]

/-- **Incondicional**: `Target ↔` nenhum zero não trivial com `Re s > 1/2`. -/
theorem target_iff_noZero_right_half : Target ↔ NoZero_right_half := by
  constructor
  · intro hRH s hz htriv hs1 hgt
    have := hRH s hz htriv hs1
    linarith
  · intro h s hz htriv hs1
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- `Re s < 1/2`: refletir para `1 − s`
      rcases le_or_gt s.re 0 with hle | hpos
      · -- `Re s ≤ 0`: então `Re(1 − s) ≥ 1` e `ζ(1 − s) ≠ 0`; pela equação funcional, `s` seria
        -- trivial ou `ζ(s) ≠ 0`.
        set w : ℂ := 1 - s with hw
        have hwre : 1 ≤ w.re := by rw [hw, Complex.sub_re, Complex.one_re]; linarith
        have hw0 : ∀ n : ℕ, w ≠ -n := by
          intro n hn
          have := congrArg Complex.re hn
          rw [Complex.neg_re, Complex.natCast_re] at this
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          linarith
        have hζw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre
        have hw1 : w ≠ 1 := by
          intro hw1
          have hs0 : s = 0 := by linear_combination -hw1 + hw
          rw [hs0, riemannZeta_zero] at hz
          norm_num at hz
        have hfe := riemannZeta_one_sub hw0 hw1
        rw [show (1 : ℂ) - w = s by rw [hw]; ring, hz] at hfe
        have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        have h2π : (2 : ℂ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero hπ
        have hpow : ((2 : ℂ) * Real.pi) ^ (-w) ≠ 0 := by
          intro hp
          rw [Complex.cpow_eq_zero_iff] at hp
          exact h2π hp.1
        have hΓ : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hw0
        have hcos : Complex.cos (Real.pi * w / 2) ≠ 0 := by
          intro hc
          obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hc
          have h2 : w * Real.pi = (2 * k + 1) * Real.pi := by linear_combination 2 * hk
          have hwk : w = 2 * k + 1 := mul_right_cancel₀ hπ h2
          have hre : w.re = 2 * (k : ℝ) + 1 := by rw [hwk]; simp
          have hk0 : (0 : ℤ) ≤ k := by
            by_contra hneg
            have : k ≤ -1 := by omega
            have : (k : ℝ) ≤ -1 := by exact_mod_cast this
            linarith
          have hk1 : k ≠ 0 := by
            intro hk0'
            apply hw1
            rw [hwk, hk0']
            simp
          apply htriv
          refine ⟨(k - 1).toNat, ?_⟩
          have hcast : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by
            have : (((k - 1).toNat : ℕ) : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
            exact_mod_cast this
          rw [hcast]
          linear_combination hw - hwk
        exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpow) hΓ) hcos)
          hζw) hfe.symm
      · -- `0 < Re s < 1/2`: `1 − s` é zero não trivial com `Re(1 − s) > 1/2`.
        have hz' := riemannZeta_one_sub_eq_zero hz hpos (by linarith)
        have hre : (1 - s).re = 1 - s.re := by simp
        refine h (1 - s) hz' (not_trivial_of_re_pos (by rw [hre]; linarith)) ?_
          (by rw [hre]; linarith)
        intro h1
        have : s = 0 := by linear_combination -h1
        rw [this, Complex.zero_re] at hpos
        exact lt_irrefl _ hpos
    · exact h s hz htriv hs1 hgt

/-- **Sanidade**: `Target → OpenAIQuasiRH78`. A hipótese externa é consequência de RH, logo não é
trivialmente falsa (refutá-la refutaria RH). -/
theorem openAIQuasiRH78_of_target (h : Target) : OpenAIQuasiRH78 := by
  intro s hz htriv hs1
  have := h s hz htriv hs1
  constructor <;> linarith

/-- **Condicional ao resultado externo**: sob `OpenAIQuasiRH78`, `Target` equivale a excluir zeros
não triviais com `1/2 < Re s ≤ 7/8`. -/
theorem target_iff_noZero_half_78 (hQ : OpenAIQuasiRH78) : Target ↔ NoZero_half_78 := by
  rw [target_iff_noZero_right_half]
  constructor
  · intro h s hz htriv hs1 hs
    exact h s hz htriv hs1 hs.1
  · intro h s hz htriv hs1 hgt
    exact h s hz htriv hs1 ⟨hgt, (hQ s hz htriv hs1).2⟩

end ClayRiemannProof
