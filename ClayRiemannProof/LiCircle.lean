import ClayRiemannProof.Xi
import ClayRiemannProof.Analogs
import Mathlib.NumberTheory.DiophantineApproximation.Basic

/-!
# O encontro das frentes: a variável de Li leva a reta ao círculo

A variável do critério de Li é `M(ρ) = 1 − 1/ρ`. Este arquivo mostra no kernel que ela é a ponte entre as frentes:

* **Reta → círculo** (`normSq_mob_eq_one_iff`, `normSq_mob_lt_one_iff`): `|1 − 1/ρ| = 1 ⟺ Re ρ = ½`, e
  `|1 − 1/ρ| < 1 ⟺ Re ρ > ½`.
* **Quarteto → quarteto de Ihara** (`mob_espelho`, `mob_tensao`, `mob_torcao`): o quarteto de Klein
  `ρ, ρ̄, 1 − ρ̄, 1 − ρ` vai em `z, z̄, 1/z̄, 1/z`, o mesmo quarteto do teorema de Ihara (`Analogs.ihara_quarteto`, `q = 1`).
* **Critério de Li quarteto a quarteto** (`li_quarteto`): a soma de Li `Σ Re(1 − wⁿ)` sobre o quarteto de `z` é
  `≥ 0` para todo `n` ⟺ `|z| = 1`. A volta usa a aproximação de Dirichlet: fora do círculo, algum `zⁿ` aponta quase
  na direção real positiva com módulo grande.
* **Clay ⟺ Li quarteto a quarteto** (`target_iff_li_quartetos`) ⟺ **ζ é "Ramanujan"** (`target_iff_ramanujan`): todo
  `1 − 1/ρ` é raiz de um trinômio real `1 − cu + u²` com `c² ≤ 4`, que é a cota de Ramanujan de Ihara e o círculo
  de Lee–Yang.
* **O encontro** (`encontro`): as cinco formulações, ξ, círculo, Li, Ramanujan e Clay, num `List.TFAE`.

**O que isto não é**: o critério de Li verdadeiro soma sobre **todos** os zeros, e a sua forma por derivadas
(`Xi.li`) só se liga à soma sobre zeros pelo produto de Hadamard (`Xi.HadamardXi`, não provado aqui). Aqui a
soma é quarteto a quarteto. Nada aqui prova RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.LiCircle

open Complex ComplexConjugate ClayRiemannProof.Zeta.Symmetry

/-! ## 1. A variável de Li -/

/-- **Variável de Li** `M(ρ) = 1 − 1/ρ`. -/
noncomputable def mob (ρ : ℂ) : ℂ := 1 - ρ⁻¹

theorem mob_eq {ρ : ℂ} (h0 : ρ ≠ 0) : mob ρ = (ρ - 1) / ρ := by
  unfold mob
  field_simp

theorem mob_ne_zero {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) : mob ρ ≠ 0 := by
  rw [mob_eq h0]
  exact div_ne_zero (sub_ne_zero.mpr h1) h0

theorem normSq_sub_one_sub (ρ : ℂ) : normSq (ρ - 1) - normSq ρ = 1 - 2 * ρ.re := by
  simp [normSq_apply]
  ring

/-- **A reta crítica vai no círculo unitário**: `|1 − 1/ρ|² = 1 ⟺ Re ρ = ½`. -/
theorem normSq_mob_eq_one_iff {ρ : ℂ} (h0 : ρ ≠ 0) : normSq (mob ρ) = 1 ↔ ρ.re = 1 / 2 := by
  rw [mob_eq h0, normSq_div, div_eq_one_iff_eq (normSq_pos.mpr h0).ne']
  have := normSq_sub_one_sub ρ
  constructor <;> intro h <;> linarith

/-- **O semiplano `Re ρ > ½` vai no disco**: `|1 − 1/ρ| < 1 ⟺ Re ρ > ½`. -/
theorem normSq_mob_lt_one_iff {ρ : ℂ} (h0 : ρ ≠ 0) : normSq (mob ρ) < 1 ↔ 1 / 2 < ρ.re := by
  rw [mob_eq h0, normSq_div, div_lt_one (normSq_pos.mpr h0)]
  have := normSq_sub_one_sub ρ
  constructor <;> intro h <;> linarith

theorem norm_eq_one_iff_normSq (w : ℂ) : ‖w‖ = 1 ↔ normSq w = 1 := by
  rw [normSq_eq_norm_sq]
  constructor
  · intro h
    rw [h]
    norm_num
  · intro h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg w) two_ne_zero).mp h

/-! ## 2. O quarteto de Klein vira o quarteto de Ihara -/

theorem mob_espelho (ρ : ℂ) : mob (espelho ρ) = conj (mob ρ) := by
  unfold mob espelho
  simp [map_sub, map_one, map_inv₀]

theorem mob_tensao {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) : mob (tensao ρ) = (mob ρ)⁻¹ := by
  have h1' : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h1'' : ρ - 1 ≠ 0 := sub_ne_zero.mpr h1
  unfold tensao
  rw [mob_eq h1', mob_eq h0, inv_div]
  field_simp
  ring

theorem mob_torcao {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) : mob (torcao ρ) = (conj (mob ρ))⁻¹ := by
  have e0 : espelho ρ ≠ 0 := by
    unfold espelho
    exact (map_ne_zero (starRingEnd ℂ)).mpr h0
  have e1 : espelho ρ ≠ 1 := by
    unfold espelho
    intro h
    apply h1
    simpa using congrArg conj h
  rw [(torcao_eq ρ).1, mob_tensao e0 e1, mob_espelho]

/-! ## 3. O critério de Li quarteto a quarteto -/

/-- **Soma de Li sobre o quarteto** `z, z̄, 1/z̄, 1/z`: `Σ Re(1 − wⁿ)`. -/
noncomputable def liQ (z : ℂ) (n : ℕ) : ℝ :=
  (1 - z ^ n).re + (1 - conj z ^ n).re + (1 - (conj z)⁻¹ ^ n).re + (1 - z⁻¹ ^ n).re

theorem liQ_eq (z : ℂ) (n : ℕ) : liQ z n = 4 - 2 * (z ^ n).re - 2 * (z⁻¹ ^ n).re := by
  unfold liQ
  have h1 : (conj z ^ n).re = (z ^ n).re := by rw [← map_pow, conj_re]
  have h2 : ((conj z)⁻¹ ^ n).re = (z⁻¹ ^ n).re := by rw [← map_inv₀, ← map_pow, conj_re]
  simp only [sub_re, one_re, h1, h2]
  ring

theorem liQ_inv (z : ℂ) (n : ℕ) : liQ z⁻¹ n = liQ z n := by
  rw [liQ_eq, liQ_eq, inv_inv]
  ring

/-- `Re zⁿ = |z|ⁿ cos(n arg z)`. -/
theorem re_pow (z : ℂ) (n : ℕ) : (z ^ n).re = ‖z‖ ^ n * Real.cos (n * arg z) := by
  conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
  rw [mul_pow, ← Complex.exp_nat_mul, ← ofReal_pow,
    show (n : ℂ) * (↑(arg z) * I) = ↑((n : ℝ) * arg z) * I by push_cast; ring,
    re_ofReal_mul, exp_ofReal_mul_I_re]

/-- **Fora do círculo, alguma potência aponta para a direita com módulo grande**: se `|z| > 1`, existe `n` com
`Re zⁿ > 2` (aproximação de Dirichlet aplicada ao ângulo). -/
theorem exists_re_pow_gt {z : ℂ} (hz : 1 < ‖z‖) : ∃ n : ℕ, 2 < (z ^ n).re := by
  obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt (4 : ℝ) hz
  obtain ⟨j, k, hk0, -, hjk⟩ :=
    Real.exists_int_int_abs_mul_sub_le ((M : ℝ) * arg z / (2 * Real.pi)) (n := 5) (by norm_num)
  refine ⟨k.toNat * M, ?_⟩
  have hk : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hk0.le
  have hn : ((k.toNat * M : ℕ) : ℝ) = (k : ℝ) * M := by rw [Nat.cast_mul, hk]
  rw [re_pow]
  set δ := 2 * Real.pi * ((k : ℝ) * ((M : ℝ) * arg z / (2 * Real.pi)) - j) with hδ
  have hpi := Real.pi_pos
  have hang : ((k.toNat * M : ℕ) : ℝ) * arg z = δ + j * (2 * Real.pi) := by
    rw [hn, hδ]
    field_simp
    ring
  have hjk' : |(k : ℝ) * ((M : ℝ) * arg z / (2 * Real.pi)) - j| ≤ 1 / 6 := by
    have := hjk
    norm_num at this ⊢
    linarith
  have hδb : |δ| ≤ Real.pi / 3 := by
    rw [hδ, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    nlinarith [abs_nonneg ((k : ℝ) * ((M : ℝ) * arg z / (2 * Real.pi)) - j)]
  have hcos : 1 / 2 ≤ Real.cos (((k.toNat * M : ℕ) : ℝ) * arg z) := by
    rw [hang, Real.cos_add_int_mul_two_pi, ← Real.cos_abs]
    have := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg δ) (by linarith) hδb
    rwa [Real.cos_pi_div_three] at this
  have hz0 : 0 < ‖z‖ := lt_trans zero_lt_one hz
  have hpow : ‖z‖ ^ M ≤ ‖z‖ ^ (k.toNat * M) := by
    apply pow_le_pow_right₀ hz.le
    have : 1 ≤ k.toNat := by omega
    exact Nat.le_mul_of_pos_left M this
  have hmul : ‖z‖ ^ (k.toNat * M) * (1 / 2) ≤
      ‖z‖ ^ (k.toNat * M) * Real.cos (((k.toNat * M : ℕ) : ℝ) * arg z) :=
    mul_le_mul_of_nonneg_left hcos (pow_nonneg hz0.le _)
  linarith

/-- Fora do círculo (`|w| > 1`) a soma de Li do quarteto fica negativa para algum `n`. -/
theorem liQ_neg {w : ℂ} (hw : 1 < ‖w‖) : ∃ n : ℕ, liQ w n < 0 := by
  obtain ⟨n, hn⟩ := exists_re_pow_gt hw
  refine ⟨n, ?_⟩
  rw [liQ_eq]
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hw
    linarith
  have hpos : 0 < (w⁻¹ ^ n).re := by
    rw [inv_pow, inv_re]
    exact div_pos (by linarith) (normSq_pos.mpr (pow_ne_zero _ hw0))
  linarith

/-- **Critério de Li quarteto a quarteto**: `Σ_{quarteto} Re(1 − wⁿ) ≥ 0` para todo `n` ⟺ `|z| = 1`. -/
theorem li_quarteto {z : ℂ} (hz : z ≠ 0) : (∀ n : ℕ, 0 ≤ liQ z n) ↔ ‖z‖ = 1 := by
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hinv : 1 < ‖z⁻¹‖ := by
        rw [norm_inv]
        exact (one_lt_inv₀ (norm_pos_iff.mpr hz)).mpr hlt
      obtain ⟨n, hn⟩ := liQ_neg hinv
      rw [liQ_inv] at hn
      exact absurd (h n) (not_le.mpr hn)
    · obtain ⟨n, hn⟩ := liQ_neg hgt
      exact absurd (h n) (not_le.mpr hn)
  · intro h n
    rw [liQ_eq, Complex.inv_eq_conj h, ← map_pow, conj_re]
    have : (z ^ n).re ≤ 1 := by
      have := Complex.re_le_norm (z ^ n)
      rwa [norm_pow, h, one_pow] at this
    linarith

/-- **A soma do quarteto é a soma dos termos de Li** `Re(1 − (1 − 1/w)ⁿ)` sobre `w ∈ {ρ, ρ̄, 1 − ρ̄, 1 − ρ}`. -/
theorem liQ_mob {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) (n : ℕ) :
    liQ (mob ρ) n = (1 - mob ρ ^ n).re + (1 - mob (espelho ρ) ^ n).re +
      (1 - mob (torcao ρ) ^ n).re + (1 - mob (tensao ρ) ^ n).re := by
  rw [mob_espelho, mob_torcao h0 h1, mob_tensao h0 h1]
  rfl

/-- Na reta, cada termo de Li `Re(1 − (1 − 1/ρ)ⁿ)` é `≥ 0`. -/
theorem li_termo_nonneg {ρ : ℂ} (h0 : ρ ≠ 0) (h : ρ.re = 1 / 2) (n : ℕ) : 0 ≤ (1 - mob ρ ^ n).re := by
  have hm : ‖mob ρ‖ = 1 := (norm_eq_one_iff_normSq _).mpr ((normSq_mob_eq_one_iff h0).mpr h)
  have := Complex.re_le_norm (mob ρ ^ n)
  rw [norm_pow, hm, one_pow] at this
  simp only [sub_re, one_re]
  linarith

/-! ## 4. As frentes se encontram -/

theorem ne_zero_of_mem_Z {ρ : ℂ} (hρ : ρ ∈ Z) : ρ ≠ 0 := by
  intro h
  have := hρ.2.1
  rw [h, zero_re] at this
  exact lt_irrefl 0 this

theorem ne_one_of_mem_Z {ρ : ℂ} (hρ : ρ ∈ Z) : ρ ≠ 1 := by
  intro h
  have := hρ.2.2
  rw [h, one_re] at this
  exact lt_irrefl 1 this

/-- **Clay ⟺ todo `1 − 1/ρ` está no círculo unitário.** -/
theorem target_iff_circulo : Target ↔ ∀ ρ ∈ Z, normSq (mob ρ) = 1 := by
  constructor
  · intro hT ρ hρ
    exact (normSq_mob_eq_one_iff (ne_zero_of_mem_Z hρ)).mpr (riemann_imp_re hT hρ)
  · intro h
    exact riemann_iff_torcao.mpr fun ρ hρ =>
      (torcao_fixo_iff ρ).mpr ((normSq_mob_eq_one_iff (ne_zero_of_mem_Z hρ)).mp (h ρ hρ))

/-- **Clay ⟺ o critério de Li vale quarteto a quarteto.** -/
theorem target_iff_li_quartetos : Target ↔ ∀ ρ ∈ Z, ∀ n : ℕ, 0 ≤ liQ (mob ρ) n := by
  rw [target_iff_circulo]
  refine forall₂_congr fun ρ hρ => ?_
  rw [li_quarteto (mob_ne_zero (ne_zero_of_mem_Z hρ) (ne_one_of_mem_Z hρ)), norm_eq_one_iff_normSq]

/-- **Clay ⟺ ζ é "Ramanujan"**: todo `u = 1 − 1/ρ` é raiz de um trinômio real `1 − cu + u²` com `c² ≤ 4`. -/
theorem target_iff_ramanujan :
    Target ↔ ∀ ρ ∈ Z, ∃ c : ℝ, c ^ 2 ≤ 4 ∧ 1 - (c : ℂ) * mob ρ + ((1 : ℝ) : ℂ) * mob ρ ^ 2 = 0 := by
  rw [target_iff_circulo]
  refine forall₂_congr fun ρ _ => ?_
  constructor
  · intro h
    refine ⟨2 * (mob ρ).re, ?_, ?_⟩
    · have := Complex.re_sq_le_normSq (mob ρ)
      nlinarith
    · have hmc := Complex.mul_conj (mob ρ)
      have hac := Complex.add_conj (mob ρ)
      rw [h] at hmc
      push_cast at hac hmc ⊢
      linear_combination (mob ρ) * hac - hmc
  · rintro ⟨c, hc, hu⟩
    have := (ClayRiemannProof.Analogs.ihara_ramanujan (q := 1) (l := c) one_pos hu).mpr (by linarith)
    rwa [one_mul] at this

/-- **O encontro das frentes**: ξ, círculo, Li quarteto a quarteto, Ramanujan e Clay são a mesma proposição. -/
theorem encontro : List.TFAE
    [ Target,
      ∀ s : ℂ, ClayRiemannProof.Xi.xi s = 0 → s.re = 1 / 2,
      ∀ ρ ∈ Z, normSq (mob ρ) = 1,
      ∀ ρ ∈ Z, ∀ n : ℕ, 0 ≤ liQ (mob ρ) n,
      ∀ ρ ∈ Z, ∃ c : ℝ, c ^ 2 ≤ 4 ∧ 1 - (c : ℂ) * mob ρ + ((1 : ℝ) : ℂ) * mob ρ ^ 2 = 0 ] := by
  tfae_have 1 ↔ 2 := ClayRiemannProof.Xi.target_iff_xi
  tfae_have 1 ↔ 3 := target_iff_circulo
  tfae_have 1 ↔ 4 := target_iff_li_quartetos
  tfae_have 1 ↔ 5 := target_iff_ramanujan
  tfae_finish

end ClayRiemannProof.LiCircle
