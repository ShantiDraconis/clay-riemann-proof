import ClayRiemannProof.EixoRiemann.Valores
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# A família que teria de fechar RH

* `familia_finita_estrita_nao_basta`: num espaço de configurações, se `ζ` está no fecho das configurações que violam
  RH (falsos zetas arbitrariamente próximos), toda família **finita** de desigualdades **estritas** contínuas que `ζ`
  satisfaz também é satisfeita por um falso zeta. O conjunto que elas definem é aberto; o de RH não contém aberto em
  volta de `ζ`.
* `meio_no_fecho`, `modelo_beta`: o modelo mínimo (a parte real `β` de um zero): nenhuma família finita estrita separa
  `β = 1/2` de todos os `β ≠ 1/2`.
* `teste_fixo_cego`: cada teste fixo é cego para alturas grandes (Riemann–Lebesgue): `ĝ(γ) → 0` com `|γ| → ∞`. Um
  quarteto na altura `γ₀ → ∞` some de qualquer teste fixo. A família precisa de testes em **todas** as alturas e escalas.
-/

open Filter Topology
open scoped FourierTransform

namespace EixoRiemann.Familia

theorem familia_finita_estrita_nao_basta {X : Type*} [TopologicalSpace X] (RH : Set X) (z : X)
    (hz : z ∈ closure RHᶜ) {ι : Type*} (s : Finset ι) (F : ι → X → ℝ) (hF : ∀ i ∈ s, Continuous (F i))
    (hpos : ∀ i ∈ s, 0 < F i z) : ∃ x, x ∉ RH ∧ ∀ i ∈ s, 0 < F i x := by
  have hU : IsOpen (⋂ i ∈ s, {x | 0 < F i x}) :=
    isOpen_biInter_finset fun i hi => isOpen_lt continuous_const (hF i hi)
  have hzU : z ∈ ⋂ i ∈ s, {x | 0 < F i x} := Set.mem_iInter₂.mpr hpos
  obtain ⟨x, hxU, hxR⟩ := mem_closure_iff.mp hz _ hU hzU
  exact ⟨x, hxR, Set.mem_iInter₂.mp hxU⟩

theorem meio_no_fecho : (1 / 2 : ℝ) ∈ closure ({1 / 2}ᶜ : Set ℝ) := by
  rw [closure_compl, interior_singleton]
  simp

/-- Nenhuma família finita de desigualdades estritas contínuas em `β` separa `β = 1/2` de todo `β ≠ 1/2`. -/
theorem modelo_beta {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ) (hF : ∀ i ∈ s, Continuous (F i))
    (hpos : ∀ i ∈ s, 0 < F i (1 / 2)) : ∃ β : ℝ, β ≠ 1 / 2 ∧ ∀ i ∈ s, 0 < F i β := by
  obtain ⟨β, hβ, h⟩ := familia_finita_estrita_nao_basta {1 / 2} (1 / 2) meio_no_fecho s F hF hpos
  exact ⟨β, hβ, h⟩

/-- Riemann–Lebesgue: cada teste fixo é cego para alturas grandes. -/
theorem teste_fixo_cego (g : ℝ → ℂ) : Tendsto (𝓕 g) (cocompact ℝ) (𝓝 0) :=
  Real.zero_at_infty_fourier g

end EixoRiemann.Familia

#print axioms EixoRiemann.Familia.familia_finita_estrita_nao_basta
#print axioms EixoRiemann.Familia.meio_no_fecho
#print axioms EixoRiemann.Familia.modelo_beta
#print axioms EixoRiemann.Familia.teste_fixo_cego
