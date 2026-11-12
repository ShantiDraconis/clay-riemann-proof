import ClayRiemannProof.EixoRiemann.Pontes
import Mathlib.Tactic.TFAE

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

end EixoRiemann

#print axioms EixoRiemann.rh_iff_rhFaixa
#print axioms EixoRiemann.rhFaixa_iff_rhF
#print axioms EixoRiemann.rh_eixo_riemann
#print axioms EixoRiemann.rh_iff_rhIdem
