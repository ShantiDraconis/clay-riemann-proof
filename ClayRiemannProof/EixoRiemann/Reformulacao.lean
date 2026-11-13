import ClayRiemannProof.EixoRiemann.Pontes
import Mathlib.Tactic.TFAE
import ClayRiemannProof.FiniteWorlds

/-!
# A Hipótese de Riemann no eixo Riemann

**Conjectura (RH no eixo Riemann).** Seja `Idem = ℂ[e]/(e² − e)`, com `ζ(z + δ·e) = (ζ(z), ζ(z + δ))`. Para
todo `N = z + δ·e` com as duas pontas na faixa crítica,
`ζ(N) = (0, 0) ⟹ Re z = 1/2 e Re δ = 0`.

Ou seja: toda ponte entre zeros não triviais é vertical.

`rh_eixo_riemann` prova no kernel que ela é **equivalente** à `RiemannHypothesis` da Mathlib, junto com as
outras quatro formas da mesma estrutura:

1. `RiemannHypothesis` (Mathlib);
2. `RHFaixa`: todo zero na faixa tem `Re = 1/2`;
3. `RHIdem`: toda ponte segura tem `Re z = 1/2` e `Re δ = 0`;
4. `RHQuarteto`: `Re s ≠ 1/2 ⟹ Q(s) = (ζ s, ζ(1 − s), ζ s̄, ζ(1 − s̄)) ≠ 0` em `ℂ⁴`;
5. `¬ PonteHorizontal`: nenhuma ponte com `δ` real não nulo segura (a do quarteto, `ρ → 1 − ρ̄`);
6. `RHF`: `|ζ(s)|² + |ζ(1 − s)|² > 0` na faixa fora da reta.

É reformulação: nenhuma das seis é provada aqui.
-/

open ClayRiemannProof.Zeta.Symmetry

namespace EixoRiemann

/-- Forma 6: `F(s) = |ζ(s)|² + |ζ(1 − s)|²` é positiva na faixa, fora da reta. -/
def RHF : Prop :=
  ∀ s : ℂ, 0 < s.re → s.re < 1 → s.re ≠ 1 / 2 → 0 < ‖riemannZeta s‖ ^ 2 + ‖riemannZeta (1 - s)‖ ^ 2

theorem rh_iff_rhFaixa : RiemannHypothesis ↔ RHFaixa := by
  unfold RHFaixa
  rw [riemann_iff_torcao]
  exact forall₂_congr fun ρ _ => torcao_fixo_iff ρ

theorem rhFaixa_iff_rhF : RHFaixa ↔ RHF := by
  constructor
  · intro h s h0 h1 hre
    have hz : riemannZeta s ≠ 0 := fun hz => hre (h s ⟨hz, h0, h1⟩)
    have hpos := norm_pos_iff.mpr hz
    linarith [pow_pos hpos 2, sq_nonneg ‖riemannZeta (1 - s)‖]
  · intro h ρ hρ
    by_contra hre
    obtain ⟨ht, -, -⟩ := tensao_mem_Z hρ
    obtain ⟨hz, h0, h1⟩ := hρ
    have ht' : riemannZeta (1 - ρ) = 0 := ht
    have hF := h ρ h0 h1 hre
    rw [hz, ht'] at hF
    simp at hF

/-- **RH no eixo Riemann**: as seis formas são equivalentes. -/
theorem rh_eixo_riemann :
    List.TFAE [RiemannHypothesis, RHFaixa, RHIdem, RHQuarteto, ¬ PonteHorizontal, RHF] := by
  tfae_have 1 ↔ 2 := rh_iff_rhFaixa
  tfae_have 2 ↔ 3 := rhIdem_iff.symm
  tfae_have 2 ↔ 4 := rhQuarteto_iff.symm
  tfae_have 2 ↔ 5 := rh_iff_sem_ponte_horizontal
  tfae_have 2 ↔ 6 := rhFaixa_iff_rhF
  tfae_finish

/-- A conjectura na forma principal: `RiemannHypothesis ⟺ RHIdem`. -/
theorem rh_iff_rhIdem : RiemannHypothesis ↔ RHIdem := rh_iff_rhFaixa.trans rhIdem_iff.symm

/-! ## O que é provável hoje: a conjectura até uma altura -/

/-- A conjectura do eixo Riemann até a altura `T`: pontes com as duas pontas em `|Im| ≤ T`. -/
def RHIdemAte (T : ℕ) : Prop :=
  ∀ x : Idem, Idem.aplica riemannZeta x = ⟨0, 0⟩ → 0 < x.z.re → x.z.re < 1 →
    0 < (x.z + x.w).re → (x.z + x.w).re < 1 → |x.z.im| ≤ T → |(x.z + x.w).im| ≤ T →
      x.z.re = 1 / 2 ∧ x.w.re = 0

/-- **Toda verificação de RH até `T` vira a conjectura do eixo Riemann até `T`.** Com
`ClayRiemannProof.Continuacao.rhAteZ_continuacao37`, isso vale para `T = 3 000 204 982 471`, condicional a
Platt–Trudgian 2021 e às janelas numéricas nomeadas. -/
theorem rhIdemAte_of_rhateZ {T : ℕ} (h : ClayRiemannProof.FiniteWorlds.RHateZ T) : RHIdemAte T := by
  have reta : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → |s.im| ≤ T → s.re = 1 / 2 := by
    intro s hz h0 h1 hT
    refine h s hz ?_ ?_ hT
    · intro ht
      exact absurd (re_trivial ht) (not_lt.mpr h0.le)
    · rintro rfl
      simp at h1
  intro x hx h0 h1 h0' h1' hT hT'
  rw [Idem.aplica_eq_zero] at hx
  have a := reta _ hx.1 h0 h1 hT
  have b := reta _ hx.2 h0' h1' hT'
  refine ⟨a, ?_⟩
  rw [Complex.add_re] at b
  linarith

end EixoRiemann

#print axioms EixoRiemann.rh_iff_rhFaixa
#print axioms EixoRiemann.rhFaixa_iff_rhF
#print axioms EixoRiemann.rh_eixo_riemann
#print axioms EixoRiemann.rh_iff_rhIdem
#print axioms EixoRiemann.rhIdemAte_of_rhateZ
