import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Báez-Duarte — os objetos concretos `χ`, `ρ_k`, `D_N`

Origem: ATK kernel (espelho público), `ATK/Conditional/Riemann.lean` (definições) e
`ATK/RiemannConcrete.lean` (monotonia e limite). Portado para Mathlib `8fe7ce4`.
Retirado na portagem: as pontes condicionais `BaezDuarteCriterion`/`UniformLogBound` (aqui a
suficiência é teorema, ver `ClayRiemannProof.BaezDuarte.Sufficiency`) e a "teoria de estados"
do ATK (`O1_iff_dissipacao`), que não é necessária para o critério.

Objetos (nada abstrato):
* `chi t = 𝟙_(0,1](t)`, `rho k t = {1/(k t)}` (parte fracionária);
* `DN N = inf_c ∫_{(0,∞)} (χ − Σ_{k=1}^{N} c_k ρ_k)²` — o quadrado da distância de Báez-Duarte.

O integrando é sempre integrável (`ClayRiemannProof.BaezDuarte.Faithful.integrable_residual`),
logo `residualSq` é a integral de Lebesgue genuína, nunca o valor-lixo `0` de Bochner.
-/

namespace ClayRiemannProof.BaezDuarte

open MeasureTheory Filter Topology Set

/-- `χ = 𝟙_(0,1]`. -/
noncomputable def chi (t : ℝ) : ℝ := Set.indicator (Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ)) t

/-- `ρ_k(t) = {1/(k t)}`. -/
noncomputable def rho (k : ℕ) (t : ℝ) : ℝ := Int.fract (1 / ((k : ℝ) * t))

/-- `‖χ − Σ_{k=1}^{N} c_k ρ_k‖²` em `L²((0,∞), dt)`. -/
noncomputable def residualSq (N : ℕ) (c : Fin N → ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), (chi t - ∑ k : Fin N, c k * rho (k.val + 1) t) ^ 2

/-- `D_N = d_N² = inf_c ‖χ − Σ_{k=1}^{N} c_k ρ_k‖²`. -/
noncomputable def DN (N : ℕ) : ℝ := ⨅ c : Fin N → ℝ, residualSq N c

theorem DN_nonneg (N : ℕ) : 0 ≤ DN N :=
  Real.iInf_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _

theorem residualSq_nonneg (N : ℕ) (c : Fin N → ℝ) : 0 ≤ residualSq N c :=
  integral_nonneg fun _ => sq_nonneg _

theorem DN_le_residualSq (N : ℕ) (c : Fin N → ℝ) : DN N ≤ residualSq N c :=
  ciInf_le ⟨0, by rintro _ ⟨c, rfl⟩; exact residualSq_nonneg N c⟩ c

/-- Acrescentar o gerador `ρ_{N+1}` com coeficiente 0 não muda o resíduo. -/
theorem residualSq_extend (N : ℕ) (c : Fin N → ℝ) :
    residualSq (N + 1) (Fin.snoc c 0) = residualSq N c := by
  unfold residualSq
  congr 1
  funext t
  rw [Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- **`D_N` é decrescente.** -/
theorem DN_antitone : Antitone DN := by
  refine antitone_nat_of_succ_le fun N => le_ciInf fun c => ?_
  exact (DN_le_residualSq (N + 1) (Fin.snoc c 0)).trans_eq (residualSq_extend N c)

theorem DN_le_DN_zero (N : ℕ) : DN N ≤ DN 0 := DN_antitone (Nat.zero_le N)

/-- `D_0 = ‖χ‖² ≤ 1`. -/
theorem DN_zero_le_one : DN 0 ≤ 1 := by
  refine (DN_le_residualSq 0 Fin.elim0).trans (le_of_eq ?_)
  unfold residualSq chi
  simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero]
  have hsq : (fun t : ℝ => (Set.indicator (Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ)) t) ^ 2) =
      Set.indicator (Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ)) := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) 1 <;> simp [ht]
  rw [hsq, integral_indicator measurableSet_Ioc]
  simp only [integral_const, smul_eq_mul, mul_one]
  rw [Measure.restrict_restrict measurableSet_Ioc]
  have : Ioc (0 : ℝ) 1 ∩ Ioi 0 = Ioc 0 1 := by
    ext x; simp only [mem_inter_iff, mem_Ioc, mem_Ioi]; constructor
    · rintro ⟨h, -⟩; exact h
    · intro h; exact ⟨h, h.1⟩
  rw [this]
  simp

theorem DN_le_one (N : ℕ) : DN N ≤ 1 := (DN_le_DN_zero N).trans DN_zero_le_one

/-- **`D_N` converge**, e o limite é `D_∞ = inf_N D_N`. -/
theorem DN_tendsto_iInf : Tendsto DN atTop (𝓝 (⨅ N, DN N)) :=
  tendsto_atTop_ciInf DN_antitone ⟨0, by rintro _ ⟨N, rfl⟩; exact DN_nonneg N⟩

/-- **`D_N → 0` ⟺ `inf_N D_N = 0`.** -/
theorem tendsto_zero_iff_iInf_eq_zero : Tendsto DN atTop (𝓝 0) ↔ ⨅ N, DN N = 0 := by
  constructor
  · intro h; exact tendsto_nhds_unique DN_tendsto_iInf h
  · intro h; rw [← h]; exact DN_tendsto_iInf

end ClayRiemannProof.BaezDuarte
