import ClayRiemannProof.CertifiedZeros.EulerMaclaurinData

/-!
# Cota grosseira certificada de `|ζ|` numa região

Para `Re w > 0`, `w ≠ 1`, `‖w‖ ≤ R` e `‖w − 1‖ ≥ d`:

  `‖ζ(w)‖ ≤ N + N/d + ½ + Σ_{j=2}^{M} |B_j|/j!·(R)_{j−1}·N^{1−j} + (R)_M/M!·C_M·N^{1−M}/(M − 1)`

(`cota_geral`), a partir de Euler–Maclaurin com resto explícito; `cotaQ` é o mesmo número em `ℚ`, calculado pelo
kernel, e `cotaQ_spec` identifica os dois.

Origem: ATK kernel (espelho público, M-Core `390e378`), trecho (§5) de `ATK/ZeroClasses/QuartoGeral.lean`
(`pochR`, `pochR_nonneg`, `norm_poch_le`, `cota_geral`, `pochRQ`, `somaBQ`, `cotaQ`, `pochRQ_spec`,
`somaBQ_spec`, `cotaQ_spec`); portado para Mathlib `8fe7ce4`, nomes `ATK.ZeroClasses.Quarto.*` →
`ClayRiemannProof.CertifiedZeros.CrudeBound.*`, linhas `#print axioms` retiradas (os axiomas estão fixados em
`ClayRiemannProof/AuditThirteen.lean`). As peças daquele arquivo específicas da reta `σ = ¼` (`seg`, `peca`,
`centros`, `chk`, …) e o seu import de `ATK/ZeroClasses/FinalAudit.lean` não são necessários e não foram portados.
-/

open Complex Metric Set

namespace ClayRiemannProof.CertifiedZeros.CrudeBound

open ClayRiemannProof.EulerMaclaurin.General ClayRiemannProof.CertifiedZeros.EulerMaclaurinData

/-! ## Cota grosseira de `ζ` -/

/-- `(R)_k = R(R+1)⋯(R+k−1)`. -/
noncomputable def pochR (R : ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => pochR R k * (R + k)

theorem pochR_nonneg {R : ℝ} (hR : 0 ≤ R) : ∀ k, 0 ≤ pochR R k
  | 0 => by simp [pochR]
  | k + 1 => by
    simp only [pochR]
    exact mul_nonneg (pochR_nonneg hR k) (by positivity)

theorem norm_poch_le {w : ℂ} {R : ℝ} (hR : ‖w‖ ≤ R) : ∀ k, ‖poch w k‖ ≤ pochR R k
  | 0 => by simp [poch, pochR]
  | k + 1 => by
    simp only [poch, pochR]
    rw [norm_mul]
    have h1 : ‖w + k‖ ≤ R + k := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_natCast]
      linarith
    exact mul_le_mul (norm_poch_le hR k) h1 (norm_nonneg _) (pochR_nonneg ((norm_nonneg w).trans hR) k)

/-- **Cota grosseira geral.** -/
theorem cota_geral {w : ℂ} {N M : ℕ} {R d : ℝ} (hN : 1 ≤ N) (hM : 2 ≤ M)
    (h0 : 0 < w.re) (hw1 : w ≠ 1) (hR : ‖w‖ ≤ R) (hd : 0 < d) (hdw : d ≤ ‖w - 1‖) :
    ‖riemannZeta w‖ ≤ N + N / d + 1 / 2 +
      (∑ j ∈ Finset.Ico 2 (M + 1), |(bernoulli j : ℝ)| / (j.factorial : ℝ) * pochR R (j - 1) *
        ((N : ℝ) ^ (j - 1))⁻¹) +
      pochR R M / (M.factorial : ℝ) * (Cb M * ((N : ℝ) ^ (M - 1))⁻¹ / ((M : ℝ) - 1)) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hNp : 0 < N := by omega
  have hR0 : 0 ≤ R := (norm_nonneg w).trans hR
  have hE := norm_zeta_sub_EM_le h0 hw1 hN (by omega : 1 ≤ M)
  have hS : ‖∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-w)‖ ≤ N := by
    refine (norm_sum_le _ _).trans ?_
    have : ∀ n ∈ Finset.range N, ‖((n : ℂ) + 1) ^ (-w)‖ ≤ 1 := by
      intro n _
      have e : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [e, Complex.norm_natCast_cpow_of_pos (by omega)]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (by omega : 1 ≤ n + 1))
      simp only [neg_re]
      linarith
    calc ∑ n ∈ Finset.range N, ‖((n : ℂ) + 1) ^ (-w)‖ ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) :=
          Finset.sum_le_sum this
      _ = N := by simp
  have hP : ‖(N : ℂ) ^ (1 - w) / (w - 1)‖ ≤ N / d := by
    rw [norm_div, Complex.norm_natCast_cpow_of_pos hNp]
    have h1 : (N : ℝ) ^ (1 - w).re ≤ N := by
      have := Real.rpow_le_rpow_of_exponent_le hN1 (show (1 - w).re ≤ 1 by simp; linarith)
      simpa using this
    have hw1n : 0 < ‖w - 1‖ := lt_of_lt_of_le hd hdw
    calc (N : ℝ) ^ (1 - w).re / ‖w - 1‖ ≤ N / ‖w - 1‖ := div_le_div_of_nonneg_right h1 hw1n.le
      _ ≤ N / d := div_le_div_of_nonneg_left hN0.le hd hdw
  have hH : ‖(N : ℂ) ^ (-w) / 2‖ ≤ 1 / 2 := by
    rw [norm_div, Complex.norm_natCast_cpow_of_pos hNp]
    have : (N : ℝ) ^ (-w).re ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1 (by simp only [neg_re]; linarith)
    rw [Complex.norm_ofNat]
    linarith
  have hJ : ‖∑ j ∈ Finset.Ico 2 (M + 1), (bernoulli j : ℂ) / (j.factorial : ℂ) * poch w (j - 1) *
      (N : ℂ) ^ (-w - ((j - 1 : ℕ) : ℂ))‖ ≤ ∑ j ∈ Finset.Ico 2 (M + 1), |(bernoulli j : ℝ)| /
        (j.factorial : ℝ) * pochR R (j - 1) * ((N : ℝ) ^ (j - 1))⁻¹ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, norm_mul, norm_div, Complex.norm_natCast_cpow_of_pos hNp]
    have hb : ‖(bernoulli j : ℂ)‖ = |(bernoulli j : ℝ)| := by
      rw [show ((bernoulli j : ℚ) : ℂ) = (((bernoulli j : ℚ) : ℝ) : ℂ) by push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs]
    have hf : ‖(j.factorial : ℂ)‖ = (j.factorial : ℝ) := Complex.norm_natCast _
    rw [hb, hf]
    have hpw : (N : ℝ) ^ (-w - ((j - 1 : ℕ) : ℂ)).re ≤ ((N : ℝ) ^ (j - 1))⁻¹ := by
      have e : (-w - ((j - 1 : ℕ) : ℂ)).re = -w.re - ((j - 1 : ℕ) : ℝ) := by simp
      rw [e]
      have := Real.rpow_le_rpow_of_exponent_le hN1
        (show -w.re - ((j - 1 : ℕ) : ℝ) ≤ -((j - 1 : ℕ) : ℝ) by linarith)
      rw [Real.rpow_neg hN0.le, Real.rpow_natCast] at this
      exact this
    have hp := norm_poch_le hR (j - 1)
    have hc : 0 ≤ |(bernoulli j : ℝ)| / (j.factorial : ℝ) := by positivity
    have hpow0 : 0 ≤ (N : ℝ) ^ (-w - ((j - 1 : ℕ) : ℂ)).re := Real.rpow_nonneg hN0.le _
    calc |(bernoulli j : ℝ)| / (j.factorial : ℝ) * ‖poch w (j - 1)‖ *
          (N : ℝ) ^ (-w - ((j - 1 : ℕ) : ℂ)).re
        ≤ |(bernoulli j : ℝ)| / (j.factorial : ℝ) * pochR R (j - 1) *
          (N : ℝ) ^ (-w - ((j - 1 : ℕ) : ℂ)).re := by gcongr
      _ ≤ |(bernoulli j : ℝ)| / (j.factorial : ℝ) * pochR R (j - 1) * ((N : ℝ) ^ (j - 1))⁻¹ := by
          gcongr
          exact mul_nonneg hc (pochR_nonneg hR0 _)
  have hrem : ‖riemannZeta w - EM N M w‖ ≤
      pochR R M / (M.factorial : ℝ) * (Cb M * ((N : ℝ) ^ (M - 1))⁻¹ / ((M : ℝ) - 1)) := by
    refine hE.trans ?_
    have hM1 : (1 : ℝ) < M := by exact_mod_cast (by omega : 1 < M)
    have hpw : (N : ℝ) ^ (1 - w.re - M) ≤ ((N : ℝ) ^ (M - 1))⁻¹ := by
      have hc : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ M)]
        simp
      have := Real.rpow_le_rpow_of_exponent_le hN1
        (show 1 - w.re - (M : ℝ) ≤ -((M - 1 : ℕ) : ℝ) by rw [hc]; linarith)
      rw [Real.rpow_neg hN0.le, Real.rpow_natCast] at this
      exact this
    have hden0 : 0 < (M : ℝ) - 1 := by linarith
    have hfac : (0 : ℝ) < M.factorial := by exact_mod_cast Nat.factorial_pos M
    have hp := norm_poch_le hR M
    have hCb := Cb_nonneg M
    have hpow0 : 0 ≤ (N : ℝ) ^ (1 - w.re - M) := Real.rpow_nonneg hN0.le _
    calc ‖poch w M‖ / (M.factorial : ℝ) * (Cb M * (N : ℝ) ^ (1 - w.re - M) / (w.re + M - 1))
        ≤ pochR R M / (M.factorial : ℝ) * (Cb M * (N : ℝ) ^ (1 - w.re - M) / (w.re + M - 1)) := by
          gcongr
          · exact div_nonneg (mul_nonneg hCb hpow0) (by linarith)
      _ ≤ pochR R M / (M.factorial : ℝ) * (Cb M * ((N : ℝ) ^ (M - 1))⁻¹ / ((M : ℝ) - 1)) := by
          apply mul_le_mul_of_nonneg_left _ (div_nonneg (pochR_nonneg hR0 M) hfac.le)
          exact div_le_div₀ (mul_nonneg hCb (by positivity)) (mul_le_mul_of_nonneg_left hpw hCb)
            hden0 (by linarith)
  have hEM : ‖EM N M w‖ ≤ N + N / d + 1 / 2 + ∑ j ∈ Finset.Ico 2 (M + 1), |(bernoulli j : ℝ)| /
      (j.factorial : ℝ) * pochR R (j - 1) * ((N : ℝ) ^ (j - 1))⁻¹ := by
    unfold EM
    have t1 := norm_add_le ((∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-w)) + (N : ℂ) ^ (1 - w) / (w - 1) -
      (N : ℂ) ^ (-w) / 2) (∑ j ∈ Finset.Ico 2 (M + 1), (bernoulli j : ℂ) / (j.factorial : ℂ) *
        poch w (j - 1) * (N : ℂ) ^ (-w - ((j - 1 : ℕ) : ℂ)))
    have t2 := norm_sub_le ((∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-w)) + (N : ℂ) ^ (1 - w) / (w - 1))
      ((N : ℂ) ^ (-w) / 2)
    have t3 := norm_add_le (∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-w)) ((N : ℂ) ^ (1 - w) / (w - 1))
    linarith
  have htri : ‖riemannZeta w‖ ≤ ‖riemannZeta w - EM N M w‖ + ‖EM N M w‖ := by
    have := norm_add_le (riemannZeta w - EM N M w) (EM N M w)
    rwa [sub_add_cancel] at this
  linarith

/-! ### O valor racional da cota -/

def pochRQ (R : ℚ) : ℕ → ℚ
  | 0 => 1
  | k + 1 => pochRQ R k * (R + k)

def somaBQ (N : ℕ) (R : ℚ) : ℕ → ℚ
  | 0 => 0
  | 1 => 0
  | M + 2 => somaBQ N R (M + 1) + |Btab (M + 2)| / ((M + 2).factorial : ℚ) * pochRQ R (M + 1) /
      (N : ℚ) ^ (M + 1)

/-- O valor racional da cota grosseira. -/
def cotaQ (N M : ℕ) (R d : ℚ) : ℚ :=
  N + N / d + 1 / 2 + somaBQ N R M +
    pochRQ R M / (M.factorial : ℚ) * (CbR M (M + 1) / (N : ℚ) ^ (M - 1) / ((M : ℚ) - 1))

theorem pochRQ_spec (R : ℚ) : ∀ k, ((pochRQ R k : ℚ) : ℝ) = pochR R k
  | 0 => by simp [pochRQ, pochR]
  | k + 1 => by
    simp only [pochRQ, pochR]
    push_cast
    rw [pochRQ_spec R k]

theorem somaBQ_spec (N : ℕ) (R : ℚ) : ∀ M : ℕ, M ≤ 10 →
    ((somaBQ N R M : ℚ) : ℝ) = ∑ j ∈ Finset.Ico 2 (M + 1), |(bernoulli j : ℝ)| / (j.factorial : ℝ) *
      pochR R (j - 1) * ((N : ℝ) ^ (j - 1))⁻¹
  | 0, _ => by simp [somaBQ]
  | 1, _ => by simp [somaBQ]
  | M + 2, hM => by
    rw [Finset.sum_Ico_succ_top (by omega : 2 ≤ M + 2), ← somaBQ_spec N R (M + 1) (by omega)]
    simp only [somaBQ]
    rw [show M + 2 - 1 = M + 1 by omega, ← pochRQ_spec R (M + 1), bern_eq (by omega : M + 2 ≤ 10)]
    push_cast
    ring

theorem cotaQ_spec {N M : ℕ} (hM : M ≤ 10) (R d : ℚ) :
    ((cotaQ N M R d : ℚ) : ℝ) = N + N / (d : ℝ) + 1 / 2 +
      (∑ j ∈ Finset.Ico 2 (M + 1), |(bernoulli j : ℝ)| / (j.factorial : ℝ) * pochR R (j - 1) *
        ((N : ℝ) ^ (j - 1))⁻¹) +
      pochR R M / (M.factorial : ℝ) * (Cb M * ((N : ℝ) ^ (M - 1))⁻¹ / ((M : ℝ) - 1)) := by
  have hCb : Cb M = ((CbR M (M + 1) : ℚ) : ℝ) := by rw [CbR_spec M hM (M + 1) le_rfl]; rfl
  unfold cotaQ
  rw [hCb, ← somaBQ_spec N R M hM, ← pochRQ_spec R M]
  push_cast
  ring

end ClayRiemannProof.CertifiedZeros.CrudeBound
