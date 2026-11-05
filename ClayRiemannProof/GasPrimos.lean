import ClayRiemannProof.Identidades
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# O gás de primos e duas pontes para a meta: `1/ζ` como traço fermiônico e os zeros triviais simples

Versão só-Mathlib das rodadas 106–107 do ATK (`atk-kernel/ATK/FracoesPrimons.lean`,
`FracoesFermions.lean`, `FracoesFermionsRH.lean`, `FracoesLinearizacao.lean`, `FracoesZerosTriviais.lean`).

1. **Gás bosônico** (`traco_bosonico`): com os modos `n ≥ 1` de energia `log n`, `Σ_{n ≤ N+1} n^{−σ} → ζ(σ)`
   para `σ > 1`: `ζ(σ) = Tr e^{−σH}`.
2. **Gás fermiônico** (`indice_witten`, `traco_fermionico`): o sinal `(−1)^F = μ(n)` dá
   `Σ_{d ∣ n} μ(d) = [n = 1]` e `Σ μ(n) n^{−s} = 1/ζ(s)` em `Re s > 1`.
3. **O critério** (`semZeros_iff_continuaAte`, para todo `θ`): `ζ ≠ 0` em `Re s > θ` ⟺ `1/ζ` tem continuação
   holomorfa a `Re s > θ`. Ida: singularidade removível em `s = 1`. Volta: princípio de identidade no semiplano
   superior convexo, `ζ(s̄) = conj ζ(s)` e continuidade na reta real.
4. **A meta** (`target_iff_semZeros`, **`target_iff_continuaAte`**, `target_iff_traco`): a meta do Clay ⟺ a
   função de partição fermiônica `1/ζ = Σ μ(n) n^{−s}` continua holomorfa até `Re s > ½`.
5. **Linearização** (`formula_exata`, `linearizacao`): `|ζ(−2m−δ)| = 2|sin(πδ/2)|·K_m(δ)` exatamente, e
   `2δK_m ≤ |ζ(−2m−δ)| ≤ πδK_m` para `0 < δ < 1`.
6. **Zeros triviais simples** (`derivada_fatorial`, `zero_trivial_simples`):
   `‖ζ′(−2m)‖ = (2m)!·|ζ(2m+1)|/(2(2π)^{2m})` e `ζ′(−2m) ≠ 0` para `m ≥ 1`.

Nada aqui prova a meta: a continuação de `Σ μ(n) n^{−s}` até `Re s > ½` é equivalente a ela (e a
`M(x) = O(x^{½+ε})`, Littlewood, não formalizado aqui), e a simplicidade dos zeros não triviais continua aberta.
`OPEN_MATH = true`.
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

namespace ClayRiemannProof.GasPrimos

open ClayRiemannProof.Zeta.Symmetry

/-! ## 1. O gás bosônico: `ζ(σ) = Tr e^{−σH}` -/

/-- Peso do modo `n` (número `n + 1`, energia `log (n + 1)`): `(n + 1)^{−σ}`. -/
noncomputable def peso (σ : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (-σ)

/-- **`ζ(σ) = Tr e^{−σH}`**: `Σ_{n ≤ N} (n + 1)^{−σ} → ζ(σ)` para `σ > 1`. -/
theorem traco_bosonico {σ : ℝ} (hσ : 1 < σ) :
    Tendsto (fun N : ℕ => ((∑ i ∈ Finset.range (N + 1), peso σ i : ℝ) : ℂ)) atTop (𝓝 (riemannZeta σ)) := by
  have hre : 1 < (σ : ℂ).re := by rw [Complex.ofReal_re]; exact hσ
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ (σ : ℂ)) := by
    have := (Complex.summable_one_div_nat_cpow (p := (σ : ℂ))).mpr hre
    exact (summable_nat_add_iff 1).mpr this |>.congr fun n => by push_cast; ring_nf
  have hterm : ∀ n : ℕ, 1 / ((n : ℂ) + 1) ^ (σ : ℂ) = ((peso σ n : ℝ) : ℂ) := by
    intro n
    unfold peso
    rw [Real.rpow_neg (by positivity), Complex.ofReal_inv, Complex.ofReal_cpow (by positivity),
      one_div]
    push_cast
    ring_nf
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hre]
  have h := hsum.hasSum.tendsto_sum_nat
  have h2 := h.comp (tendsto_add_atTop_nat 1)
  refine h2.congr fun N => ?_
  simp only [Function.comp_apply, Complex.ofReal_sum, hterm]

section Fermions

open scoped LSeries.notation ArithmeticFunction.Moebius

/-! ## 2. O gás fermiônico: índice de Witten e traço `Σ μ(n) n^{−s} = 1/ζ(s)` -/

/-- **Índice de Witten**: `Σ_{d ∣ n} μ(d) = 1` se `n = 1` e `0` caso contrário. -/
theorem indice_witten (n : ℕ) :
    ∑ d ∈ n.divisors, ArithmeticFunction.moebius d = if n = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
    ArithmeticFunction.one_apply]

/-- **Traço fermiônico**: `L(μ, s) = 1/ζ(s)` em `Re s > 1`. -/
theorem traco_fermionico_eq {s : ℂ} (hs : 1 < s.re) : LSeries ↗μ s = (riemannZeta s)⁻¹ := by
  have h := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at h
  exact eq_inv_of_mul_eq_one_right h

/-- O traço fermiônico como soma convergente: `Σ μ(n) n^{−s} = 1/ζ(s)` em `Re s > 1`. -/
theorem traco_fermionico {s : ℂ} (hs : 1 < s.re) : LSeriesHasSum ↗μ s (riemannZeta s)⁻¹ := by
  rw [← traco_fermionico_eq hs]
  exact (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).LSeriesHasSum

/-! ## 3. O critério: sem zeros em `Re s > θ` ⟺ `1/ζ` continua até `Re s > θ` -/

/-- `ζ` sem zeros em `Re s > θ`. -/
def SemZeros (θ : ℝ) : Prop := ∀ s : ℂ, θ < s.re → riemannZeta s ≠ 0

/-- A função de partição fermiônica `1/ζ` continua holomorfa até `Re s > θ`. -/
def ContinuaAte (θ : ℝ) : Prop :=
  ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {s | θ < s.re} ∧ ∀ s : ℂ, 1 < s.re → F s * riemannZeta s = 1

/-- `1/ζ(s) → 0` quando `s → 1` (o polo vira zero). -/
theorem inv_zeta_tende_zero : Tendsto (fun s => (riemannZeta s)⁻¹) (𝓝[≠] 1) (𝓝 0) := by
  have h1 : Tendsto (fun s : ℂ => s - 1) (𝓝[≠] 1) (𝓝 0) := by
    have := ((tendsto_id (x := 𝓝 (1 : ℂ))).sub_const (1 : ℂ)).mono_left
      (nhdsWithin_le_nhds (s := {(1 : ℂ)}ᶜ))
    simpa using this
  have h2 := riemannZeta_residue_one.inv₀ one_ne_zero
  have h3 := h1.mul h2
  rw [zero_mul] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hs1, one_mul]

/-- A continuação explícita: `1/ζ` com o valor `0` em `s = 1`. -/
noncomputable def inversa : ℂ → ℂ := Function.update (fun s => (riemannZeta s)⁻¹) 1 0

theorem inversa_de_ne {s : ℂ} (hs : s ≠ 1) : inversa s = (riemannZeta s)⁻¹ :=
  Function.update_of_ne hs _ _

/-- **Ida**: sem zeros em `Re s > θ` ⇒ `1/ζ` continua até `Re s > θ`. -/
theorem continuaAte_of_semZeros {θ : ℝ} (h : SemZeros θ) : ContinuaAte θ := by
  have hopen : IsOpen {s : ℂ | θ < s.re} := isOpen_lt continuous_const continuous_re
  have hdiff : ∀ z : ℂ, θ < z.re → z ≠ 1 → DifferentiableAt ℂ inversa z := by
    intro z hz hz1
    have hd : DifferentiableAt ℂ (fun s => (riemannZeta s)⁻¹) z :=
      (differentiableAt_riemannZeta hz1).inv (h z hz)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hz1] with w hw
    exact inversa_de_ne hw
  refine ⟨inversa, fun z hz => ?_, fun s hs => ?_⟩
  · refine DifferentiableAt.differentiableWithinAt ?_
    rcases eq_or_ne z 1 with rfl | hz1
    · have hc : ContinuousAt inversa 1 := by
        unfold inversa
        rw [continuousAt_update_same]
        exact inv_zeta_tende_zero
      have hd : ∀ᶠ w in 𝓝[≠] (1 : ℂ), DifferentiableAt ℂ inversa w := by
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hopen.mem_nhds hz)] with w hw hwθ
        exact hdiff w hwθ hw
      exact (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd hc).differentiableAt
    · exact hdiff z hz hz1
  · have hs1 : s ≠ 1 := by
      rintro rfl
      simp at hs
    rw [inversa_de_ne hs1]
    exact inv_mul_cancel₀ (riemannZeta_ne_zero_of_one_le_re hs.le)

/-- O semiplano superior `{Re s > θ, Im s > 0}`. -/
def U (θ : ℝ) : Set ℂ := {s | θ < s.re ∧ 0 < s.im}

theorem U_aberto (θ : ℝ) : IsOpen (U θ) :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_const continuous_im)

theorem U_convexo (θ : ℝ) : Convex ℝ (U θ) := by
  have h1 : Convex ℝ {s : ℂ | θ < s.re} := convex_halfSpace_re_gt θ
  have h2 : Convex ℝ {s : ℂ | 0 < s.im} := convex_halfSpace_im_gt 0
  exact h1.inter h2

/-- **Chave**: se `F·ζ = 1` em `Re s > 1` e `F` é holomorfa em `Re s > θ`, então `F·ζ = 1` em todo ponto
`s ≠ 1` com `Re s > θ` e `Im s ≥ 0`. -/
theorem chave {θ : ℝ} {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F {s | θ < s.re})
    (h1 : ∀ s : ℂ, 1 < s.re → F s * riemannZeta s = 1) {s : ℂ} (hs : θ < s.re) (him : 0 ≤ s.im)
    (hs1 : s ≠ 1) : F s * riemannZeta s = 1 := by
  have hopen : IsOpen {s : ℂ | θ < s.re} := isOpen_lt continuous_const continuous_re
  set G : ℂ → ℂ := fun z => F z * riemannZeta z - 1 with hG
  -- G holomorfa no semiplano superior
  have hGd : DifferentiableOn ℂ G (U θ) := by
    intro z hz
    have hz1 : z ≠ 1 := by
      rintro rfl
      simp [U] at hz
    have hFz : DifferentiableAt ℂ F z := (hF z hz.1).differentiableAt (hopen.mem_nhds hz.1)
    exact ((hFz.mul (differentiableAt_riemannZeta hz1)).sub_const 1).differentiableWithinAt
  have hGa : AnalyticOnNhd ℂ G (U θ) := hGd.analyticOnNhd (U_aberto θ)
  -- um ponto de U com Re > 1
  set z₀ : ℂ := ((max θ 1 + 1 : ℝ) : ℂ) + I with hz₀
  have hz₀re : z₀.re = max θ 1 + 1 := by simp [hz₀]
  have hz₀im : z₀.im = 1 := by simp [hz₀]
  have hz₀U : z₀ ∈ U θ := ⟨by rw [hz₀re]; linarith [le_max_left θ 1], by rw [hz₀im]; norm_num⟩
  have hev : G =ᶠ[𝓝 z₀] 0 := by
    have hmem : {z : ℂ | 1 < z.re} ∈ 𝓝 z₀ :=
      (isOpen_lt continuous_const continuous_re).mem_nhds
        (by show 1 < z₀.re; rw [hz₀re]; linarith [le_max_right θ 1])
    filter_upwards [hmem] with z hz
    simp [hG, h1 z hz]
  have hzero : EqOn G 0 (U θ) :=
    hGa.eqOn_zero_of_preconnected_of_eventuallyEq_zero (U_convexo θ).isPreconnected hz₀U hev
  -- s está no fecho de U
  have hcl : s ∈ closure (U θ) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨s + ((ε / 2 : ℝ) : ℂ) * I, ⟨?_, ?_⟩, ?_⟩
    · simpa using hs
    · simp; linarith
    · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
  -- G contínua em s
  have hFs : DifferentiableAt ℂ F s := (hF s hs).differentiableAt (hopen.mem_nhds hs)
  have hGc : ContinuousAt G s :=
    ((hFs.mul (differentiableAt_riemannZeta hs1)).sub_const 1).continuousAt
  have himg := hGc.continuousWithinAt.mem_closure_image hcl
  have hsub : G '' U θ ⊆ {0} := by
    rintro _ ⟨z, hz, rfl⟩
    exact hzero hz
  have hGs : G s = 0 := by
    have := closure_mono hsub himg
    rwa [closure_singleton, mem_singleton_iff] at this
  simpa [hG, sub_eq_zero] using hGs

/-- **Volta**: `1/ζ` continua até `Re s > θ` ⇒ sem zeros em `Re s > θ`. -/
theorem semZeros_of_continuaAte {θ : ℝ} (h : ContinuaAte θ) : SemZeros θ := by
  obtain ⟨F, hF, h1⟩ := h
  intro s hs hz
  rcases eq_or_ne s 1 with rfl | hs1
  · exact riemannZeta_one_ne_zero hz
  rcases le_or_gt 0 s.im with him | him
  · have := chave hF h1 hs him hs1
    rw [hz, mul_zero] at this
    exact zero_ne_one this
  · -- o conjugado está no semiplano superior e também é zero
    have hc : riemannZeta (conj s) = 0 := by rw [riemannZeta_conj, hz, map_zero]
    have hcre : θ < (conj s).re := by rwa [conj_re]
    have hcim : 0 ≤ (conj s).im := by rw [conj_im]; linarith
    have hc1 : conj s ≠ 1 := by
      intro he
      have : (conj s).im = 0 := by rw [he]; simp
      rw [conj_im] at this
      linarith
    have := chave hF h1 hcre hcim hc1
    rw [hc, mul_zero] at this
    exact zero_ne_one this

/-- **O critério**: `ζ` não tem zeros em `Re s > θ` ⟺ `1/ζ` continua holomorfa até `Re s > θ`. -/
theorem semZeros_iff_continuaAte (θ : ℝ) : SemZeros θ ↔ ContinuaAte θ :=
  ⟨continuaAte_of_semZeros, semZeros_of_continuaAte⟩

/-- O critério dito com o traço fermiônico `Σ μ(n) n^{−s}`. -/
theorem continuaAte_iff_traco (θ : ℝ) : ContinuaAte θ ↔
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {s | θ < s.re} ∧ ∀ s : ℂ, 1 < s.re → F s = LSeries ↗μ s := by
  refine exists_congr fun F => and_congr_right fun _ => forall_congr' fun s => imp_congr_right fun hs => ?_
  rw [traco_fermionico_eq hs]
  have hz := riemannZeta_ne_zero_of_one_le_re hs.le
  constructor
  · intro h; exact eq_inv_of_mul_eq_one_left h
  · intro h; rw [h]; exact inv_mul_cancel₀ hz

/-- Monotonia: continuar até `θ` dá continuação até todo `θ' ≥ θ`. -/
theorem continuaAte_mono {θ θ' : ℝ} (h : θ ≤ θ') (hθ : ContinuaAte θ) : ContinuaAte θ' := by
  obtain ⟨F, hF, h1⟩ := hθ
  exact ⟨F, hF.mono fun s hs => lt_of_le_of_lt h hs, h1⟩

/-- Sempre vale até `θ = 1` (Hadamard–de la Vallée Poussin, Mathlib). -/
theorem continuaAte_um : ContinuaAte 1 :=
  continuaAte_of_semZeros fun _ hs => riemannZeta_ne_zero_of_one_le_re hs.le

/-! ## 4. A meta -/

/-- **A meta ⟺ `ζ` sem zeros em `Re s > ½`** (a torção leva `Re < ½` em `Re > ½`). -/
theorem target_iff_semZeros : Target ↔ SemZeros (1 / 2) := by
  constructor
  · intro hT s hs hz
    have hre1 : s.re < 1 := by
      by_contra h1
      exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h1) hz
    have hsZ : s ∈ Z := ⟨hz, by linarith, hre1⟩
    exact (Identidades.nao_target_iff.mpr ⟨torcao s, torcao_mem_Z hsZ, by rw [re_torcao]; linarith⟩) hT
  · intro h
    by_contra hT
    obtain ⟨ρ, hρ, hre⟩ := Identidades.nao_target_iff.mp hT
    exact h (torcao ρ) (by rw [re_torcao]; linarith) (torcao_mem_Z hρ).1

/-- **A meta ⟺ `1/ζ` continua holomorfa até `Re s > ½`.** -/
theorem target_iff_continuaAte : Target ↔ ContinuaAte (1 / 2) :=
  target_iff_semZeros.trans (semZeros_iff_continuaAte _)

/-- A meta dita com o traço fermiônico `Σ μ(n) n^{−s}`. -/
theorem target_iff_traco : Target ↔
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F {s | 1 / 2 < s.re} ∧ ∀ s : ℂ, 1 < s.re → F s = LSeries ↗μ s :=
  target_iff_continuaAte.trans (continuaAte_iff_traco _)

end Fermions

/-! ## 5. A lei de linearização perto dos zeros triviais -/

/-- `a(x) = |ζ(x)|` na reta real. -/
noncomputable def a (x : ℝ) : ℝ := ‖riemannZeta (x : ℂ)‖

/-- O fator `K_m(δ) = (2π)^{−(2m+1+δ)}·Γ(2m+1+δ)·|ζ(2m+1+δ)|`. -/
noncomputable def K (m : ℕ) (δ : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(2 * (m : ℝ) + 1 + δ)) * Real.Gamma (2 * m + 1 + δ) * a (2 * m + 1 + δ)

theorem K_pos (m : ℕ) {δ : ℝ} (hδ0 : 0 < δ) : 0 < K m δ := by
  have hm : (0 : ℝ) ≤ m := m.cast_nonneg
  unfold K
  have h1 : 0 < (2 * Real.pi) ^ (-(2 * (m : ℝ) + 1 + δ)) := Real.rpow_pos_of_pos (by positivity) _
  have h2 : 0 < Real.Gamma (2 * m + 1 + δ) := Real.Gamma_pos_of_pos (by linarith)
  have h3 : 0 < a (2 * m + 1 + δ) := by
    unfold a
    exact norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by rw [ofReal_re]; linarith))
  positivity

/-- **Fórmula exata**: `|ζ(−2m − δ)| = 2·|sin(πδ/2)|·K_m(δ)`. -/
theorem formula_exata (m : ℕ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    a (-(2 * m + δ)) = 2 * |Real.sin (Real.pi * δ / 2)| * K m δ := by
  have hm : (0 : ℝ) ≤ m := m.cast_nonneg
  set σ : ℝ := 2 * m + 1 + δ with hσ
  have h0 : ∀ n : ℕ, (σ : ℂ) ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have h1 : (σ : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have e := riemannZeta_one_sub h0 h1
  have ec : (1 - (σ : ℂ)) = ((-(2 * m + δ) : ℝ) : ℂ) := by rw [hσ]; push_cast; ring
  rw [ec] at e
  unfold K a
  rw [← hσ, e]
  have hb : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have hc : (Real.pi : ℂ) * (σ : ℂ) / 2 = ((Real.pi * σ / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hb, hc, ← Complex.ofReal_cos, Complex.Gamma_ofReal, norm_mul, norm_mul, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.Gamma_pos_of_pos (by linarith : (0 : ℝ) < σ))]
  have hre : (-(σ : ℂ)).re = -σ := by simp
  rw [hre]
  have hcos : |Real.cos (Real.pi * σ / 2)| = |Real.sin (Real.pi * δ / 2)| := by
    have e1 : Real.pi * σ / 2 = (Real.pi * δ / 2 + Real.pi / 2) + m * Real.pi := by rw [hσ]; ring
    rw [e1, Real.cos_add_nat_mul_pi, Real.cos_add_pi_div_two, abs_mul, abs_pow, abs_neg, abs_neg,
      abs_one, one_pow, one_mul]
  rw [hcos, show ‖(2 : ℂ)‖ = 2 by simp]
  ring

/-- **Lei linear de dois lados**: `2δ·K_m(δ) ≤ |ζ(−2m − δ)| ≤ πδ·K_m(δ)` para `0 < δ < 1`. -/
theorem linearizacao (m : ℕ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    2 * δ * K m δ ≤ a (-(2 * m + δ)) ∧ a (-(2 * m + δ)) ≤ Real.pi * δ * K m δ := by
  rw [formula_exata m hδ0 hδ1]
  have hK := (K_pos m hδ0).le
  have hx0 : 0 ≤ Real.pi * δ / 2 := by positivity
  have hx1 : Real.pi * δ / 2 ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hs0 : 0 ≤ Real.sin (Real.pi * δ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx0 (by linarith [Real.pi_pos])
  rw [abs_of_nonneg hs0]
  have l := Real.mul_le_sin hx0 hx1
  have u := Real.sin_le hx0
  have e : 2 / Real.pi * (Real.pi * δ / 2) = δ := by field_simp
  rw [e] at l
  constructor
  · nlinarith
  · nlinarith

/-! ## 6. Os dois limites do lado direito -/

/-- `2|sin(πδ/2)|/δ → π` quando `δ → 0⁺`. -/
theorem seno_sobre :
    Tendsto (fun δ : ℝ => 2 * |Real.sin (Real.pi * δ / 2)| / δ) (𝓝[>] 0) (𝓝 Real.pi) := by
  have hlo : Tendsto (fun δ : ℝ => Real.pi - Real.pi ^ 3 * δ ^ 2 / 24) (𝓝[>] 0) (𝓝 Real.pi) := by
    have h : Tendsto (fun δ : ℝ => Real.pi - Real.pi ^ 3 * δ ^ 2 / 24) (𝓝 0)
        (𝓝 (Real.pi - Real.pi ^ 3 * 0 ^ 2 / 24)) :=
      ((continuous_const.sub ((continuous_const.mul (continuous_id.pow 2)).div_const 24)).tendsto 0)
    rw [show Real.pi - Real.pi ^ 3 * 0 ^ 2 / 24 = Real.pi by ring] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    have hx : 0 < Real.pi * δ / 2 := by positivity
    have hs := Real.sin_gt_sub_cube hx
    rw [le_div_iff₀ hδ]
    calc (Real.pi - Real.pi ^ 3 * δ ^ 2 / 24) * δ
        = 2 * (Real.pi * δ / 2 - (Real.pi * δ / 2) ^ 3 / 6) := by ring
      _ ≤ 2 * Real.sin (Real.pi * δ / 2) := by linarith
      _ ≤ 2 * |Real.sin (Real.pi * δ / 2)| := by linarith [le_abs_self (Real.sin (Real.pi * δ / 2))]
  · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    have hx : 0 ≤ Real.pi * δ / 2 := by positivity
    have h1 : |Real.sin (Real.pi * δ / 2)| ≤ Real.pi * δ / 2 := by
      have := Real.abs_sin_le_abs (x := Real.pi * δ / 2)
      rwa [abs_of_nonneg hx] at this
    rw [div_le_iff₀ hδ]
    linarith

/-- `K_m` é contínua em `δ = 0` para `m ≥ 1`. -/
theorem K_tende (m : ℕ) (hm : 1 ≤ m) : Tendsto (K m) (𝓝[>] 0) (𝓝 (K m 0)) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc : ContinuousAt (K m) 0 := by
    unfold K
    have h1 : ContinuousAt (fun δ : ℝ => (2 * Real.pi) ^ (-(2 * (m : ℝ) + 1 + δ))) 0 :=
      ContinuousAt.rpow continuousAt_const (by fun_prop) (Or.inl (by positivity))
    have h2 : ContinuousAt (fun δ : ℝ => Real.Gamma (2 * m + 1 + δ)) 0 := by
      have hg : ContinuousAt Real.Gamma (2 * m + 1 + 0) := by
        refine (Real.differentiableAt_Gamma fun n => ?_).continuousAt
        have : (0 : ℝ) ≤ n := n.cast_nonneg
        intro h
        linarith
      exact hg.comp (f := fun δ : ℝ => 2 * (m : ℝ) + 1 + δ) (by fun_prop)
    have h3 : ContinuousAt (fun δ : ℝ => a (2 * m + 1 + δ)) 0 := by
      unfold a
      have hz : ContinuousAt riemannZeta (((2 * m + 1 + 0 : ℝ)) : ℂ) := by
        refine (differentiableAt_riemannZeta ?_).continuousAt
        intro h
        have := congrArg Complex.re h
        simp at this
        linarith
      have hz' : ContinuousAt (fun δ : ℝ => riemannZeta ((2 * m + 1 + δ : ℝ) : ℂ)) 0 :=
        hz.comp (f := fun δ : ℝ => ((2 * m + 1 + δ : ℝ) : ℂ)) (by fun_prop)
      exact hz'.norm
    exact (h1.mul h2).mul h3
  exact hc.tendsto.mono_left nhdsWithin_le_nhds

/-! ## 7. O lado esquerdo: a derivada na direção real -/

/-- `ζ(−2m) = 0` para `m ≥ 1`, com o argumento real. -/
theorem zeta_menos_dois_m (m : ℕ) (hm : 1 ≤ m) : riemannZeta ((-(2 * m : ℝ) : ℝ) : ℂ) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have := riemannZeta_neg_two_mul_nat_add_one k
  convert this using 2
  push_cast
  ring

theorem nao_um (m : ℕ) : ((-(2 * m : ℝ) : ℝ) : ℂ) ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  have : (0 : ℝ) ≤ m := m.cast_nonneg
  linarith

/-- A derivada complexa em `−2m`, lida pela função real `x ↦ ζ(x)`. -/
theorem zeta_real_hasDerivAt (m : ℕ) :
    HasDerivAt (fun x : ℝ => riemannZeta (x : ℂ)) (deriv riemannZeta ((-(2 * m : ℝ) : ℝ) : ℂ))
      (-(2 * m : ℝ)) :=
  ((differentiableAt_riemannZeta (nao_um m)).hasDerivAt).comp_ofReal

/-- `a(−(2m + δ))/δ → ‖ζ′(−2m)‖` quando `δ → 0⁺`. -/
theorem quociente_tende (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun δ : ℝ => a (-(2 * m + δ)) / δ) (𝓝[>] 0)
      (𝓝 ‖deriv riemannZeta ((-(2 * m : ℝ) : ℝ) : ℂ)‖) := by
  have h := (zeta_real_hasDerivAt m).tendsto_slope_zero_left
  have hneg : Tendsto (fun δ : ℝ => -δ) (𝓝[>] 0) (𝓝[<] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have := ((continuous_neg (G := ℝ)).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
      show -δ < 0
      linarith
  have h2 := (h.comp hneg).norm
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
  simp only [Function.comp_apply]
  rw [zeta_menos_dois_m m hm, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs, abs_neg,
    abs_of_pos hδ, a, inv_mul_eq_div]
  congr 3
  push_cast
  ring

/-! ## 8. A derivada exata e a simplicidade dos zeros triviais -/

/-- **`‖ζ′(−2m)‖ = π·K_m(0)`** para `m ≥ 1`. -/
theorem derivada_exata (m : ℕ) (hm : 1 ≤ m) :
    ‖deriv riemannZeta ((-(2 * m : ℝ) : ℝ) : ℂ)‖ = Real.pi * K m 0 := by
  have hR : Tendsto (fun δ : ℝ => a (-(2 * m + δ)) / δ) (𝓝[>] 0) (𝓝 (Real.pi * K m 0)) := by
    have := (seno_sobre.mul (K_tende m hm))
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ
      (hδ : 0 < δ) hδ1
    rw [formula_exata m hδ hδ1.2]
    field_simp
  exact tendsto_nhds_unique (quociente_tende m hm) hR

/-- `K_m(0) = (2m)!·|ζ(2m+1)|/(2π)^{2m+1}`. -/
theorem K_zero (m : ℕ) :
    K m 0 = (Nat.factorial (2 * m) : ℝ) * a (2 * m + 1) / (2 * Real.pi) ^ (2 * m + 1) := by
  unfold K
  have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have e1 : (2 * Real.pi) ^ (-(2 * (m : ℝ) + 1 + 0)) = ((2 * Real.pi) ^ (2 * m + 1))⁻¹ := by
    rw [Real.rpow_neg hpos.le, add_zero, ← Real.rpow_natCast]
    push_cast
    ring_nf
  have e2 : Real.Gamma (2 * (m : ℝ) + 1 + 0) = (Nat.factorial (2 * m) : ℝ) := by
    rw [add_zero, ← Real.Gamma_nat_eq_factorial]
    push_cast
    ring_nf
  rw [e1, e2, add_zero]
  field_simp

/-- **`‖ζ′(−2m)‖ = (2m)!·|ζ(2m+1)|/(2(2π)^{2m})`** para `m ≥ 1` (a fórmula clássica). -/
theorem derivada_fatorial (m : ℕ) (hm : 1 ≤ m) :
    ‖deriv riemannZeta ((-(2 * m : ℝ) : ℝ) : ℂ)‖ =
      (Nat.factorial (2 * m) : ℝ) * a (2 * m + 1) / (2 * (2 * Real.pi) ^ (2 * m)) := by
  rw [derivada_exata m hm, K_zero, pow_succ]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- `|ζ(2m+1)| > 0`. -/
theorem a_impar_pos (m : ℕ) (hm : 1 ≤ m) : 0 < a (2 * m + 1) := by
  unfold a
  refine norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_le_re ?_)
  have : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [Complex.ofReal_re]
  linarith

/-- **Os zeros triviais são simples**: `ζ′(−2m) ≠ 0` para todo `m ≥ 1`. -/
theorem zero_trivial_simples (m : ℕ) (hm : 1 ≤ m) :
    deriv riemannZeta ((-(2 * m : ℝ) : ℝ) : ℂ) ≠ 0 := by
  intro h
  have := derivada_fatorial m hm
  rw [h, norm_zero] at this
  have hp : 0 < (Nat.factorial (2 * m) : ℝ) * a (2 * m + 1) / (2 * (2 * Real.pi) ^ (2 * m)) := by
    have := a_impar_pos m hm
    positivity
  linarith

/-- Exemplo: `|ζ′(−2)| = ζ(3)/(4π²)`. -/
theorem derivada_menos_dois :
    ‖deriv riemannZeta ((-(2 * (1 : ℕ) : ℝ) : ℝ) : ℂ)‖ = a 3 / (4 * Real.pi ^ 2) := by
  rw [derivada_fatorial 1 le_rfl]
  norm_num
  ring

end ClayRiemannProof.GasPrimos
