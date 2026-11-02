import ClayRiemannProof.Cert.Transcendental
import ClayRiemannProof.EulerMaclaurin.General

/-!
# Dados racionais de Euler–Maclaurin para a avaliação certificada de `ζ`

As peças computáveis (em `ℚ`, decididas pelo kernel) com que se monta o retângulo certificado de `ζ(σ + it)`:

* `Lg`, `fase`: `log m` por somas telescópicas da série de `atanh` (`mem_Lg`) e a fase `θ = −t log m`;
* `Btab` (Bernoulli `B₀,…,B₁₀`, `bern_eq`), `pochQ` (fatorial ascendente `(s)_m`, `pochQ_spec`),
  `PcR`/`Qcoef` (a parte de Bernoulli de `EM_{N,M}`, `PcR_spec`) e `CbR` (a constante `C_M` do resto, `CbR_spec`);
* `EM_decomp`: `EM_{N,M}(s) = Σ_{n<N} (n+1)^{−s} + N^{−s}·(N/(s−1) − ½ + Σ_j …)`.

Origem: ATK kernel (espelho público, M-Core `390e378`), trechos de `ATK/ZeroCertificado.lean` (`Lg`, `fase`,
`Btab`, `pochQ`, `PcR`, `Qcoef`, `CbR`, `mem_Lg`, `bp6`, `bp8`, `bp10`, `bern_eq`, `pochQ_spec`, `PcR_spec`,
`CbR_spec`, `EM_decomp`); portado para Mathlib `8fe7ce4`, nomes `ATK.ZeroCert.*` →
`ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.*`, linhas `#print axioms` retiradas (os axiomas estão
fixados em `ClayRiemannProof/AuditThirteen.lean`). O resto daquele arquivo (a avaliação na reta `σ = ½` e o
zero certificado perto de `½ + 14,1347i`) não é necessário aqui e não foi portado.
-/

open Complex Metric Set

namespace ClayRiemannProof.CertifiedZeros.EulerMaclaurinData

open ClayRiemannProof.Cert.Interval ClayRiemannProof.Cert.Transcendental
  ClayRiemannProof.EulerMaclaurin.General

/-! ## 1. Definições computáveis -/

/-- `log n` com arredondamento para fora. -/
def Lg (K p : ℕ) : ℕ → IR
  | 0 => ⟨0, 0⟩
  | 1 => ⟨0, 0⟩
  | j + 2 => IR.round p (IR.add (Lg K p (j + 1)) (dLog K (j + 1)))

/-- Fase `θ = −t log m`. -/
def fase (K p : ℕ) (t : ℚ) (m : ℕ) : IR := IR.mul (IR.pt (-t)) (Lg K p m)

/-- Bernoulli `B₀,…,B₁₀` (convenção do Mathlib, `B₁ = −½`). -/
def Btab : ℕ → ℚ
  | 0 => 1 | 1 => -1 / 2 | 2 => 1 / 6 | 4 => -1 / 30 | 6 => 1 / 42 | 8 => -1 / 30
  | 10 => 5 / 66 | _ => 0

/-- `(s)_m` para `s = a + ib`, como (re, im). -/
def pochQ (a b : ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | m + 1 => ((pochQ a b m).1 * (a + m) - (pochQ a b m).2 * b,
      (pochQ a b m).1 * b + (pochQ a b m).2 * (a + m))

/-- `P_M = Σ_{j ∈ [2, M]} B_j/j! (s)_{j−1} N^{−(j−1)}`. -/
def PcR (N : ℕ) (a b : ℚ) : ℕ → ℚ × ℚ
  | 0 => (0, 0)
  | 1 => (0, 0)
  | M + 2 =>
    ((PcR N a b (M + 1)).1 + Btab (M + 2) / ((M + 2).factorial : ℚ) / (N : ℚ) ^ (M + 1) *
        (pochQ a b (M + 1)).1,
     (PcR N a b (M + 1)).2 + Btab (M + 2) / ((M + 2).factorial : ℚ) / (N : ℚ) ^ (M + 1) *
        (pochQ a b (M + 1)).2)

/-- `Q = N/(s−1) − ½ + P_M`. -/
def Qcoef (N M : ℕ) (a b : ℚ) : ℚ × ℚ :=
  ((N : ℚ) * (a - 1) / ((a - 1) ^ 2 + b ^ 2) - 1 / 2 + (PcR N a b M).1,
   -(N : ℚ) * b / ((a - 1) ^ 2 + b ^ 2) + (PcR N a b M).2)

/-- `Σ_{i<k} |B_i| C(M,i)`. -/
def CbR (M : ℕ) : ℕ → ℚ
  | 0 => 0
  | k + 1 => CbR M k + |Btab k| * (M.choose k : ℚ)

/-! ## 2. Correção das peças -/

theorem mem_Lg (K p : ℕ) : ∀ n : ℕ, 1 ≤ n → IR.mem (Real.log n) (Lg K p n)
  | 0, h => absurd h (by norm_num)
  | 1, _ => by simp [Lg, IR.mem]
  | j + 2, _ => by
    have ih := mem_Lg K p (j + 1) (by omega)
    have hd := mem_dLog K (j := j + 1) (by omega)
    have e : Real.log ((j + 2 : ℕ) : ℝ) =
        Real.log ((j + 1 : ℕ) : ℝ) + (Real.log ((j + 1 : ℕ) + 1) - Real.log ((j + 1 : ℕ) : ℝ)) := by
      push_cast; ring_nf
    rw [e]
    simp only [Lg]
    exact IR.mem_round p (IR.mem_add ih (by push_cast at hd ⊢; exact hd))

/-! ### Bernoulli -/

theorem bp6 : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four,
    bernoulli'_eq_zero_of_odd (n := 5) ⟨2, rfl⟩ (by norm_num)]
  norm_num [Nat.choose]

theorem bp8 : bernoulli' 8 = -1 / 30 := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bp6,
    bernoulli'_eq_zero_of_odd (n := 5) ⟨2, rfl⟩ (by norm_num),
    bernoulli'_eq_zero_of_odd (n := 7) ⟨3, rfl⟩ (by norm_num)]
  norm_num [Nat.choose]

theorem bp10 : bernoulli' 10 = 5 / 66 := by
  rw [bernoulli'_def]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, bernoulli'_zero, bernoulli'_one,
    bernoulli'_two, bernoulli'_three, bernoulli'_four, bp6, bp8,
    bernoulli'_eq_zero_of_odd (n := 5) ⟨2, rfl⟩ (by norm_num),
    bernoulli'_eq_zero_of_odd (n := 7) ⟨3, rfl⟩ (by norm_num),
    bernoulli'_eq_zero_of_odd (n := 9) ⟨4, rfl⟩ (by norm_num)]
  norm_num [Nat.choose]

theorem bern_eq {j : ℕ} (hj : j ≤ 10) : bernoulli j = Btab j := by
  have odd0 : ∀ n, Odd n → 1 < n → bernoulli n = 0 := fun n h1 h2 => bernoulli_eq_zero_of_odd h1 h2
  have ev : ∀ n, n ≠ 1 → bernoulli n = bernoulli' n := fun n h => bernoulli_eq_bernoulli'_of_ne_one h
  interval_cases j
  · simp [Btab]
  · simp [Btab]
  · simp [Btab]
  · rw [odd0 3 ⟨1, rfl⟩ (by norm_num)]; rfl
  · rw [ev 4 (by norm_num), bernoulli'_four]; rfl
  · rw [odd0 5 ⟨2, rfl⟩ (by norm_num)]; rfl
  · rw [ev 6 (by norm_num), bp6]; rfl
  · rw [odd0 7 ⟨3, rfl⟩ (by norm_num)]; rfl
  · rw [ev 8 (by norm_num), bp8]; rfl
  · rw [odd0 9 ⟨4, rfl⟩ (by norm_num)]; rfl
  · rw [ev 10 (by norm_num), bp10]; rfl

/-! ### Pochhammer, `P`, `C_M` -/

theorem pochQ_spec (a b : ℚ) : ∀ m : ℕ,
    (((pochQ a b m).1 : ℚ) : ℂ) + (((pochQ a b m).2 : ℚ) : ℂ) * I = poch ((a : ℂ) + (b : ℂ) * I) m
  | 0 => by simp [pochQ, poch]
  | m + 1 => by
    rw [poch, ← pochQ_spec a b m]
    simp only [pochQ]
    push_cast
    ring_nf
    rw [I_sq]
    ring

theorem PcR_spec (N : ℕ) (a b : ℚ) : ∀ M : ℕ, M ≤ 10 →
    (((PcR N a b M).1 : ℚ) : ℂ) + (((PcR N a b M).2 : ℚ) : ℂ) * I =
      ∑ j ∈ Finset.Ico 2 (M + 1), (bernoulli j : ℂ) / (j.factorial : ℂ) *
        poch ((a : ℂ) + (b : ℂ) * I) (j - 1) * ((N : ℂ) ^ (j - 1))⁻¹
  | 0, _ => by simp [PcR]
  | 1, _ => by simp [PcR]
  | M + 2, hM => by
    rw [Finset.sum_Ico_succ_top (by omega : 2 ≤ M + 2), ← PcR_spec N a b (M + 1) (by omega)]
    simp only [PcR]
    rw [show M + 2 - 1 = M + 1 by omega, ← pochQ_spec a b (M + 1), bern_eq (by omega : M + 2 ≤ 10)]
    push_cast
    ring

theorem CbR_spec (M : ℕ) (hM : M ≤ 10) : ∀ k : ℕ, k ≤ M + 1 →
    ((CbR M k : ℚ) : ℝ) = ∑ i ∈ Finset.range k, |(bernoulli i : ℝ)| * (M.choose i : ℝ)
  | 0, _ => by simp [CbR]
  | k + 1, hk => by
    rw [Finset.sum_range_succ, ← CbR_spec M hM k (by omega)]
    simp only [CbR]
    rw [bern_eq (by omega : k ≤ 10)]
    push_cast
    ring

/-! ### Decomposição de EM -/

theorem EM_decomp {N : ℕ} (hN : 1 ≤ N) (M : ℕ) (s : ℂ) :
    EM N M s = (∑ n ∈ Finset.range N, ((n : ℂ) + 1) ^ (-s)) + (N : ℂ) ^ (-s) *
      ((N : ℂ) / (s - 1) - 1 / 2 + ∑ j ∈ Finset.Ico 2 (M + 1), (bernoulli j : ℂ) /
        (j.factorial : ℂ) * poch s (j - 1) * ((N : ℂ) ^ (j - 1))⁻¹) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have h1 : (N : ℂ) ^ (1 - s) = N * (N : ℂ) ^ (-s) := by
    rw [show 1 - s = 1 + (-s) by ring, Complex.cpow_add _ _ hN0, Complex.cpow_one]
  have h2 : ∀ j : ℕ, (N : ℂ) ^ (-s - ((j - 1 : ℕ) : ℂ)) = (N : ℂ) ^ (-s) * ((N : ℂ) ^ (j - 1))⁻¹ := by
    intro j
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hN0]
    congr 1
    rw [Complex.cpow_neg, Complex.cpow_natCast]
  unfold EM
  rw [h1]
  have h3 : ∑ j ∈ Finset.Ico 2 (M + 1), (bernoulli j : ℂ) / (j.factorial : ℂ) * poch s (j - 1) *
      (N : ℂ) ^ (-s - ((j - 1 : ℕ) : ℂ)) = (N : ℂ) ^ (-s) * ∑ j ∈ Finset.Ico 2 (M + 1),
        (bernoulli j : ℂ) / (j.factorial : ℂ) * poch s (j - 1) * ((N : ℂ) ^ (j - 1))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h2]
    ring
  rw [h3]
  ring

end ClayRiemannProof.CertifiedZeros.EulerMaclaurinData
