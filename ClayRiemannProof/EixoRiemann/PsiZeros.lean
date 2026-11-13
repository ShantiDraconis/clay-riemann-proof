import ClayRiemannProof.EixoRiemann.Familia
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Controle do caos dos primos ⟹ região sem zeros ⟹ pontes curtas

`E(n) = Λ(n) − 1`, `∑_{k ≤ n} E(k) = ψ(n) − n` (`soma_erro`). A hipótese nomeada

  `ControlePsi θ : ψ(n) − n = O(n^θ)`

é o "controle do caos dos primos no expoente `θ`".

* `lseries_erro`: em `Re s > 1`, `∑ E(n) n^{−s} = −ζ'(s)/ζ(s) − ζ(s)`.
* `F_holomorfa`: sob `ControlePsi θ`, `F(s) = s · 𝓜[R](−s)` (com `R(t) = ψ(t) − ⌊t⌋` para `t > 1`) é holomorfa em
  `Re s > θ` (`mellin_differentiableAt_of_isBigO_rpow`).
* `identidade`: em `Re s > 1`, `−ζ'/ζ − ζ = F` (somação de Abel, `LSeries_eq_mul_integral`).
* `sem_zeros_acima`: **`ControlePsi θ` (com `θ ≥ 0`) ⟹ `ζ(ρ) ≠ 0` para `Re ρ > θ`.** A identidade
  `ζ' + ζ(ζ + F) = 0` passa de `Re s > 1` para o conjunto conexo `{Re s > θ} ∖ {1}` (princípio da identidade); num
  zero `ρ` de ordem `n + 1`, `ζ = (s − ρ)^{n+1} g` com `g(ρ) ≠ 0`, e a identidade dá
  `(s − ρ)^n · ((n + 1) g + (s − ρ)(g' + g(ζ + F))) = 0` perto de `ρ`; o segundo fator vale `(n + 1) g(ρ) ≠ 0` em `ρ`.
* `controle_psi_faixa`, `controle_psi_pontes`: com `quase_rh_iff_pontes`, controle no expoente `θ` ⟹ toda ponte
  horizontal tem `|δ| ≤ 2θ − 1`.
* `rh_de_controle_psi`: `ψ(x) − x = O(x^{1/2 + ε})` para todo `ε > 0` ⟹ RH.
* `controle_psi_abaixo_do_meio`: havendo um zero na faixa, nenhum controle com `θ < 1/2` vale.

A direção recíproca (RH ⟹ `ψ(x) − x = O(x^{1/2} log² x)`, von Koch) não está aqui: ela pede a fórmula explícita
truncada (Perron), que a Mathlib ainda não tem. `ψ(x) − x = O(x^{1/2})` exatamente é **falso** (Littlewood: oscila
como `x^{1/2} log log log x`), por isso o enunciado com RH usa todo `θ > 1/2`.
-/

open Filter Topology Asymptotics MeasureTheory
open ClayRiemannProof.Zeta.Symmetry

namespace EixoRiemann.PsiZeros

/-- `E(n) = Λ(n) − 1`. -/
noncomputable def erro (n : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt n : ℂ) - 1

/-- `∑_{k=1}^{n} E(k) = ψ(n) − n`. -/
theorem soma_erro (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, erro k
      = (∑ k ∈ Finset.Icc 1 n, (ArithmeticFunction.vonMangoldt k : ℂ)) - n := by
  simp [erro, Finset.sum_sub_distrib]

/-- **Controle do caos dos primos no expoente `θ`**: `ψ(n) − n = O(n^θ)`. -/
def ControlePsi (θ : ℝ) : Prop :=
  (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, erro k) =O[atTop] fun n ↦ (n : ℝ) ^ θ

/-- Em `Re s > 1`: `∑ E(n) n^{−s} = −ζ'(s)/ζ(s) − ζ(s)`. -/
theorem lseries_erro {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable erro s ∧
      LSeries erro s = -deriv riemannZeta s / riemannZeta s - riemannZeta s := by
  have h1 : LSeriesSummable (fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have h2 : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have he : erro = (fun n : ℕ ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) - 1 := rfl
  rw [he]
  refine ⟨h1.sub h2, ?_⟩
  rw [LSeries_sub h1 h2, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    LSeries_one_eq_riemannZeta hs]

/-- Versão em variável real: `ψ(t) − ⌊t⌋ = O(t^θ)`. -/
theorem controle_real {θ : ℝ} (hθ : 0 ≤ θ) (h : ControlePsi θ) :
    (fun t : ℝ ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, erro k) =O[atTop] fun t ↦ t ^ θ :=
  (h.comp_tendsto tendsto_nat_floor_atTop).trans <|
    isEquivalent_nat_floor.isBigO.rpow hθ (eventually_ge_atTop 0)

/-- `R(t) = ψ(t) − ⌊t⌋` para `t > 1`; `0` em `(−∞, 1]`. -/
noncomputable def resto : ℝ → ℂ :=
  Set.indicator (Set.Ioi 1) fun t ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, erro k

theorem resto_mensuravel : Measurable resto := by
  have h : Measurable fun t : ℝ ↦ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, erro k :=
    (measurable_from_nat (f := fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, erro k)).comp Nat.measurable_floor
  exact h.indicator measurableSet_Ioi

theorem resto_localmente_integravel : LocallyIntegrableOn resto (Set.Ioi 0) := by
  refine LocallyIntegrable.locallyIntegrableOn ?_ _
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.bddAbove
  refine Measure.integrableOn_of_bounded
    (M := ∑ n ∈ Finset.range (⌊R⌋₊ + 1), ‖∑ k ∈ Finset.Icc 1 n, erro k‖)
    hK.measure_lt_top.ne resto_mensuravel.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with t ht
  by_cases h1 : t ∈ Set.Ioi (1 : ℝ)
  · rw [resto, Set.indicator_of_mem h1]
    exact Finset.single_le_sum (f := fun n ↦ ‖∑ k ∈ Finset.Icc 1 n, erro k‖)
      (fun n _ ↦ norm_nonneg _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_le_floor (hR ht))))
  · rw [resto, Set.indicator_of_notMem h1, norm_zero]
    exact Finset.sum_nonneg fun n _ ↦ norm_nonneg _

theorem resto_topo {θ : ℝ} (hθ : 0 ≤ θ) (h : ControlePsi θ) :
    resto =O[atTop] fun t : ℝ ↦ t ^ θ := by
  refine EventuallyEq.trans_isBigO ?_ (controle_real hθ h)
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
  rw [resto, Set.indicator_of_mem (show t ∈ Set.Ioi (1 : ℝ) from ht)]

theorem resto_base (b : ℝ) : resto =O[𝓝[>] (0 : ℝ)] fun t : ℝ ↦ t ^ (-b) := by
  refine EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (zero_lt_one' ℝ))] with t ht
  rw [resto, Set.indicator_of_notMem (show t ∉ Set.Ioi (1 : ℝ) from fun h1 ↦ lt_asymm (Set.mem_Iio.mp ht) (Set.mem_Ioi.mp h1))]

/-- `F(s) = s · ∫₁^∞ R(t) t^{−s−1} dt = s · 𝓜[R](−s)`. -/
noncomputable def F (s : ℂ) : ℂ := s * mellin resto (-s)

/-- Sob `ControlePsi θ`, `F` é holomorfa em `Re s > θ`. -/
theorem F_holomorfa {θ : ℝ} (hθ : 0 ≤ θ) (h : ControlePsi θ) {s : ℂ} (hs : θ < s.re) :
    DifferentiableAt ℂ F s := by
  have hm : DifferentiableAt ℂ (mellin resto) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (a := -θ) (b := -s.re - 1) resto_localmente_integravel
      (by simpa only [neg_neg] using resto_topo hθ h) (by rw [Complex.neg_re]; linarith)
      (resto_base _) (by rw [Complex.neg_re]; linarith)
  have hneg : DifferentiableAt ℂ (fun z : ℂ ↦ -z) s := differentiableAt_id.neg
  show DifferentiableAt ℂ (fun z : ℂ ↦ z * mellin resto (-z)) s
  exact differentiableAt_id.mul (hm.comp s hneg)

theorem integral_eq_mellin (s : ℂ) :
    ∫ t in Set.Ioi (1 : ℝ), (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, erro k) * (t : ℂ) ^ (-(s + 1))
      = mellin resto (-s) := by
  have h : mellin resto (-s) = ∫ t in Set.Ioi (0 : ℝ),
      (Set.Ioi (1 : ℝ)).indicator
        (fun t : ℝ ↦ (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, erro k) * (t : ℂ) ^ (-(s + 1))) t := by
    unfold mellin
    congr 1
    funext t
    by_cases ht : t ∈ Set.Ioi (1 : ℝ)
    · simp only [resto, Set.indicator_of_mem ht, smul_eq_mul]
      rw [show -s - 1 = -(s + 1) by ring]
      ring
    · simp only [resto, Set.indicator_of_notMem ht, smul_zero]
  rw [h, integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Set.inter_eq_left.mpr (Set.Ioi_subset_Ioi zero_le_one)]

/-- Em `Re s > 1` (e `Re s > θ`): `−ζ'(s)/ζ(s) − ζ(s) = F(s)`. -/
theorem identidade {θ : ℝ} (hθ : 0 ≤ θ) (h : ControlePsi θ) {s : ℂ} (hs : 1 < s.re)
    (hθs : θ < s.re) :
    -deriv riemannZeta s / riemannZeta s - riemannZeta s = F s := by
  obtain ⟨hsum, heq⟩ := lseries_erro hs
  rw [← heq, LSeries_eq_mul_integral erro hθ hθs hsum h, integral_eq_mellin]
  rfl

/-- `{Re s > θ} ∖ {1}` é conexo (`θ < 1`): união de quatro convexos encadeados. -/
theorem semiplano_furado {θ : ℝ} (hθ : θ < 1) :
    IsPreconnected ({s : ℂ | θ < s.re} ∩ {1}ᶜ) := by
  have hA : IsPreconnected ({s : ℂ | θ < s.re} ∩ {s | 0 < s.im}) :=
    ((convex_halfSpace_re_gt θ).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hB : IsPreconnected ({s : ℂ | θ < s.re} ∩ {s | s.im < 0}) :=
    ((convex_halfSpace_re_gt θ).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hC : IsPreconnected {s : ℂ | 1 < s.re} := (convex_halfSpace_re_gt 1).isPreconnected
  have hD : IsPreconnected ({s : ℂ | θ < s.re} ∩ {s | s.re < 1}) :=
    ((convex_halfSpace_re_gt θ).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have hU : {s : ℂ | θ < s.re} ∩ {1}ᶜ =
      ((({s : ℂ | θ < s.re} ∩ {s | 0 < s.im}) ∪ {s | 1 < s.re}) ∪
        ({s : ℂ | θ < s.re} ∩ {s | s.im < 0})) ∪ ({s : ℂ | θ < s.re} ∩ {s | s.re < 1}) := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_union]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_trichotomy s.im 0 with hi | hi | hi
      · exact Or.inl (Or.inr ⟨h1, hi⟩)
      · rcases lt_trichotomy s.re 1 with hr | hr | hr
        · exact Or.inr ⟨h1, hr⟩
        · exact absurd (Complex.ext (z := s) (w := 1) (by simpa using hr) (by simpa using hi)) h2
        · exact Or.inl (Or.inl (Or.inr hr))
      · exact Or.inl (Or.inl (Or.inl ⟨h1, hi⟩))
    · rintro (((⟨h1, hi⟩ | hr) | ⟨h1, hi⟩) | ⟨h1, hr⟩)
      · exact ⟨h1, fun h ↦ by rw [h] at hi; simp at hi⟩
      · exact ⟨by linarith, fun h ↦ by rw [h] at hr; simp at hr⟩
      · exact ⟨h1, fun h ↦ by rw [h] at hi; simp at hi⟩
      · exact ⟨h1, fun h ↦ by rw [h] at hr; simp at hr⟩
  rw [hU]
  have p1 : (⟨2, 1⟩ : ℂ) ∈ {s : ℂ | θ < s.re} ∩ {s | 0 < s.im} :=
    Set.mem_inter (show θ < 2 by linarith) (show (0 : ℝ) < 1 by norm_num)
  have p2 : (⟨2, 1⟩ : ℂ) ∈ {s : ℂ | 1 < s.re} := show (1 : ℝ) < 2 by norm_num
  have p3 : (⟨2, -1⟩ : ℂ) ∈ {s : ℂ | 1 < s.re} := show (1 : ℝ) < 2 by norm_num
  have p4 : (⟨2, -1⟩ : ℂ) ∈ {s : ℂ | θ < s.re} ∩ {s | s.im < 0} :=
    Set.mem_inter (show θ < 2 by linarith) (show (-1 : ℝ) < 0 by norm_num)
  have p5 : (⟨(θ + 1) / 2, 1⟩ : ℂ) ∈ {s : ℂ | θ < s.re} ∩ {s | 0 < s.im} :=
    Set.mem_inter (show θ < (θ + 1) / 2 by linarith) (show (0 : ℝ) < 1 by norm_num)
  have p6 : (⟨(θ + 1) / 2, 1⟩ : ℂ) ∈ {s : ℂ | θ < s.re} ∩ {s | s.re < 1} :=
    Set.mem_inter (show θ < (θ + 1) / 2 by linarith) (show (θ + 1) / 2 < 1 by linarith)
  have hAC := IsPreconnected.union _ p1 p2 hA hC
  have hACB := IsPreconnected.union _ (Set.mem_union_right _ p3) p4 hAC hB
  exact IsPreconnected.union _ (Set.mem_union_left _ (Set.mem_union_left _ p5)) p6 hACB hD

/-- **Controle do caos dos primos no expoente `θ` ⟹ nenhum zero de `ζ` com `Re ρ > θ`.** -/
theorem sem_zeros_acima {θ : ℝ} (hθ : 0 ≤ θ) (h : ControlePsi θ) {ρ : ℂ} (hρ : θ < ρ.re) :
    riemannZeta ρ ≠ 0 := by
  intro hz
  have hρ1 : ρ.re < 1 := by
    by_contra hge
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hge) hz
  have hθ1 : θ < 1 := hρ.trans hρ1
  have hρne : ρ ≠ 1 := by
    rintro rfl
    simp at hρ1
  have hρc : ρ ∈ ({1}ᶜ : Set ℂ) := Set.mem_compl_singleton_iff.mpr hρne
  have h2c : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := Set.mem_compl_singleton_iff.mpr (by norm_num)
  have hζ2 : riemannZeta 2 ≠ 0 := riemannZeta_ne_zero_of_one_le_re Nat.one_le_ofNat
  -- (1) a identidade `ζ' + ζ (ζ + F) = 0` em todo `{Re > θ} ∖ {1}`
  have hFan : AnalyticOnNhd ℂ F {s : ℂ | θ < s.re} :=
    DifferentiableOn.analyticOnNhd (fun s hs ↦ (F_holomorfa hθ h hs).differentiableWithinAt)
      (isOpen_lt continuous_const Complex.continuous_re)
  have hHan : AnalyticOnNhd ℂ
      (fun s ↦ deriv riemannZeta s + riemannZeta s * (riemannZeta s + F s))
      ({s : ℂ | θ < s.re} ∩ {1}ᶜ) := by
    intro s hs
    have a1 : AnalyticAt ℂ (deriv riemannZeta) s := analyticOn_riemannZeta.deriv s hs.2
    have a2 : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs.2
    have a3 : AnalyticAt ℂ F s := hFan s hs.1
    exact a1.add (a2.mul (a2.add a3))
  have h2U : (2 : ℂ) ∈ {s : ℂ | θ < s.re} ∩ {1}ᶜ :=
    ⟨show θ < (2 : ℂ).re by rw [Complex.re_ofNat]; linarith, h2c⟩
  have hH2 : (fun s ↦ deriv riemannZeta s + riemannZeta s * (riemannZeta s + F s))
      =ᶠ[𝓝 (2 : ℂ)] 0 := by
    have hmem : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by rw [Complex.re_ofNat]; norm_num)
    filter_upwards [hmem] with s hs
    have hs' : 1 < s.re := hs
    have hne := riemannZeta_ne_zero_of_one_le_re hs'.le
    have hid := identidade hθ h hs' (by linarith)
    have h1 : -deriv riemannZeta s / riemannZeta s = riemannZeta s + F s := by
      linear_combination hid
    rw [div_eq_iff hne] at h1
    show deriv riemannZeta s + riemannZeta s * (riemannZeta s + F s) = 0
    linear_combination -h1
  have hEq := hHan.eqOn_zero_of_preconnected_of_eventuallyEq_zero (semiplano_furado hθ1) h2U hH2
  have hUo : IsOpen ({s : ℂ | θ < s.re} ∩ {1}ᶜ) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_compl_singleton
  have hρU : ρ ∈ {s : ℂ | θ < s.re} ∩ {1}ᶜ := ⟨hρ, hρc⟩
  have hHρ : ∀ᶠ z in 𝓝 ρ, deriv riemannZeta z + riemannZeta z * (riemannZeta z + F z) = 0 := by
    filter_upwards [hUo.mem_nhds hρU] with z hz
    exact hEq hz
  -- (2) `ζ` não se anula identicamente perto de `ρ` (senão seria `0` em `ℂ ∖ {1}`, e `ζ(2) ≠ 0`)
  have hnot : ¬ ∀ᶠ z in 𝓝 ρ, riemannZeta z = 0 := by
    intro hev
    exact hζ2 (analyticOn_riemannZeta.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected hρc hev h2c)
  -- (3) `ζ(z) = (z − ρ)^n g(z)` com `g(ρ) ≠ 0`
  obtain ⟨n, g, hg, hgρ, hev⟩ :=
    (analyticOn_riemannZeta ρ hρc).exists_eventuallyEq_pow_smul_ne_zero_iff.mpr hnot
  cases n with
  | zero =>
    have h0 := hev.self_of_nhds
    rw [hz, pow_zero, one_smul] at h0
    exact hgρ h0.symm
  | succ m =>
    have hev' : ∀ᶠ z in 𝓝 ρ, riemannZeta z = (z - ρ) ^ (m + 1) * g z :=
      hev.mono fun z hz' ↦ by rw [hz', smul_eq_mul]
    have hevd : deriv riemannZeta =ᶠ[𝓝 ρ] deriv (fun z ↦ (z - ρ) ^ (m + 1) * g z) :=
      Filter.EventuallyEq.deriv hev'
    have hdP : ∀ z, AnalyticAt ℂ g z →
        deriv (fun w ↦ (w - ρ) ^ (m + 1) * g w) z
          = ((m + 1 : ℕ) : ℂ) * (z - ρ) ^ m * g z + (z - ρ) ^ (m + 1) * deriv g z := by
      intro z hgz
      have hsub : HasDerivAt (fun w : ℂ ↦ w - ρ) 1 z :=
        (hasDerivAt_sub_const_iff ρ).mpr (hasDerivAt_id' (x := z))
      have hpow := hsub.pow (m + 1)
      rw [Nat.add_sub_cancel, mul_one] at hpow
      have hprod : HasDerivAt (fun w ↦ (w - ρ) ^ (m + 1) * g w)
          (((m + 1 : ℕ) : ℂ) * (z - ρ) ^ m * g z + (z - ρ) ^ (m + 1) * deriv g z) z :=
        hpow.mul hgz.differentiableAt.hasDerivAt
      exact hprod.deriv
    have hkc : ContinuousAt (fun z ↦ ((m + 1 : ℕ) : ℂ) * g z
        + (z - ρ) * (deriv g z + g z * (riemannZeta z + F z))) ρ := by
      have c1 : ContinuousAt g ρ := hg.continuousAt
      have c2 : ContinuousAt (deriv g) ρ := hg.deriv.continuousAt
      have c3 : ContinuousAt riemannZeta ρ := (differentiableAt_riemannZeta hρne).continuousAt
      have c4 : ContinuousAt F ρ := (F_holomorfa hθ h hρ).continuousAt
      exact (continuousAt_const.mul c1).add
        ((continuousAt_id.sub continuousAt_const).mul (c2.add (c1.mul (c3.add c4))))
    have hk0 : ((m + 1 : ℕ) : ℂ) * g ρ
        + (ρ - ρ) * (deriv g ρ + g ρ * (riemannZeta ρ + F ρ)) ≠ 0 := by
      rw [sub_self, zero_mul, add_zero]
      exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)) hgρ
    have hkne := hkc.eventually_ne hk0
    have hall : ∀ᶠ z in 𝓝 ρ, (z - ρ) ^ m = 0 := by
      filter_upwards [hHρ, hev', hevd, hg.eventually_analyticAt, hkne] with z hH hzz hdz hgz hkz
      have hd := hdP z hgz
      have hkey : (z - ρ) ^ m * (((m + 1 : ℕ) : ℂ) * g z
          + (z - ρ) * (deriv g z + g z * (riemannZeta z + F z))) = 0 := by
        linear_combination hH - hdz - hd - (riemannZeta z + F z) * hzz
      exact (mul_eq_zero.mp hkey).resolve_right hkz
    obtain ⟨z, hz0, hzne⟩ := ((hall.filter_mono nhdsWithin_le_nhds).and
      (eventually_mem_nhdsWithin (s := {ρ}ᶜ) (a := ρ))).exists
    exact pow_ne_zero m (sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hzne)) hz0

/-- Controle no expoente `θ` ⟹ todo zero da faixa tem `Re ρ ≤ θ`. -/
theorem controle_psi_faixa {θ : ℝ} (hθ : 0 ≤ θ) (h : ControlePsi θ) : ∀ ρ ∈ Z, ρ.re ≤ θ :=
  fun _ hρ ↦ not_lt.mp fun hlt ↦ sem_zeros_acima hθ h hlt hρ.1

/-- Controle no expoente `θ` ⟹ toda ponte horizontal `s, s + r` entre zeros tem `|r| ≤ 2θ − 1`. -/
theorem controle_psi_pontes {θ : ℝ} (hθ : 0 ≤ θ) (h : ControlePsi θ) :
    ∀ (s : ℂ) (r : ℝ), s ∈ Z → s + (r : ℂ) ∈ Z → |r| ≤ 2 * θ - 1 :=
  (Valores.quase_rh_iff_pontes θ).mp (controle_psi_faixa hθ h)

/-- `ψ(x) − x = O(x^{1/2 + ε})` para todo `ε > 0` ⟹ RH. -/
theorem rh_de_controle_psi (h : ∀ θ : ℝ, 1 / 2 < θ → ControlePsi θ) : RiemannHypothesis := by
  rw [rh_iff_rhFaixa]
  intro ρ hρ
  by_contra hne
  have hd : 0 < |ρ.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hθ : (1 : ℝ) / 2 < 1 / 2 + |ρ.re - 1 / 2| / 2 := by linarith
  have := (Valores.faixa_simetrica _).mp (controle_psi_faixa (by linarith) (h _ hθ)) ρ hρ
  linarith

/-- Havendo um zero na faixa, nenhum controle com `0 ≤ θ < 1/2` vale. -/
theorem controle_psi_abaixo_do_meio {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < 1 / 2) (hZ : Z.Nonempty) :
    ¬ ControlePsi θ :=
  fun h ↦ Valores.abaixo_do_meio_falso hθ hZ (controle_psi_faixa hθ0 h)

end EixoRiemann.PsiZeros
