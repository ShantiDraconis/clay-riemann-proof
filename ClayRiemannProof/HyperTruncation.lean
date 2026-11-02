import ClayRiemannProof.BaezDuarteGap
import Mathlib.Analysis.Real.Hyperreal

/-!
# O truncamento depois do infinito: `D_ω`

O critério de Báez-Duarte trunca em `N` termos (`DN N`). Aqui o truncamento é feito num inteiro
**depois de todos os inteiros comuns**: o hipernatural `ω = [n ↦ n]` dos hiper-reais `ℝ*` da Mathlib
(`Hyperreal.omega`, maior que todo real, `Hyperreal.coe_lt_omega`). O valor de `D` nesse truncamento é
`D_ω = [n ↦ DN n] ∈ ℝ*`.

* **`target_iff_DOmega_infinitesimal`**: o enunciado do Clay ⟺ `D_ω` é infinitesimal
  (menor que todo real positivo).

Ou seja: RH é exatamente "a distância de Báez-Duarte truncada depois do infinito é infinitamente
pequena". Não existe um primeiro inteiro infinito (se `N` é infinito, `N − 1` também é), então `ω` não é
"o" ponto depois do infinito: é um representante. Isto é uma reformulação de `target_iff_gap`, **não**
uma prova de RH: decidir se `D_ω` é infinitesimal é o mesmo problema. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.HyperTruncation

open Filter Topology Hyperreal ClayRiemannProof.BaezDuarte

/-- `D` truncado no inteiro infinito `ω`. -/
noncomputable def DOmega : ℝ* := ofSeq (fun n => DN n)

/-- `x` é infinitesimal: `|x|` é menor que todo real positivo. -/
def IsInfinitesimal (x : ℝ*) : Prop := ∀ r : ℝ, 0 < r → |x| < r

theorem DOmega_nonneg : 0 ≤ DOmega := by
  have h : ofSeq (fun _ => (0 : ℝ)) ≤ DOmega :=
    ofSeq_le_ofSeq.2 (Eventually.of_forall fun n => DN_nonneg n)
  exact h

/-- **O truncamento depois do infinito**: Clay ⟺ `D_ω` é infinitesimal. -/
theorem target_iff_DOmega_infinitesimal : Target ↔ IsInfinitesimal DOmega := by
  rw [target_iff_gap, gap_iff_tendsto]
  constructor
  · intro hT r hr
    rw [abs_of_nonneg DOmega_nonneg]
    have hev : ∀ᶠ n in atTop, DN n < r :=
      (hT.eventually (gt_mem_nhds hr))
    exact ofSeq_lt_ofSeq.2 (Nat.hyperfilter_le_atTop hev)
  · intro h
    rw [tendsto_zero_iff_iInf_eq_zero]
    refine le_antisymm (le_of_forall_pos_lt_add fun r hr => ?_)
      (le_ciInf fun n => DN_nonneg n)
    have hlt : DOmega < (r : ℝ*) := by
      have := h r hr
      rwa [abs_of_nonneg DOmega_nonneg] at this
    have hev : ∀ᶠ n in hyperfilter ℕ, DN n < r :=
      ofSeq_lt_ofSeq.1 (show ofSeq (fun n => DN n) < ofSeq (fun _ => r) from hlt)
    obtain ⟨n, hn⟩ := hev.exists
    have hb : BddBelow (Set.range DN) := ⟨0, by rintro _ ⟨m, rfl⟩; exact DN_nonneg m⟩
    calc (⨅ m, DN m) ≤ DN n := ciInf_le hb n
      _ < 0 + r := by linarith

/-- `ω` vem **depois de todos os inteiros comuns**: `n < ω` para todo `n : ℕ`. -/
theorem nat_lt_omega (n : ℕ) : ((n : ℝ) : ℝ*) < ω := coe_lt_omega n

/-- **Não existe primeiro inteiro infinito**: `ω − 1` também está depois de todos os inteiros comuns, então o
corte entre os inteiros comuns e os infinitos não tem último elemento de um lado nem primeiro do outro. -/
theorem nat_lt_omega_sub_one (n : ℕ) : ((n : ℝ) : ℝ*) < ω - 1 := by
  have h := coe_lt_omega ((n : ℝ) + 1)
  have : ((((n : ℝ) + 1 : ℝ)) : ℝ*) = ((n : ℝ) : ℝ*) + 1 := by push_cast; ring
  rw [this] at h
  linarith

end ClayRiemannProof.HyperTruncation
