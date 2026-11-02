import ClayRiemannProof.Main
import ClayRiemannProof.Fronteira.Li
import ClayRiemannProof.Fronteira.Ht

/-!
# O objeto desejado e o que falta para chegar nele

O alvo é `ClayRiemannProof.Target` (= `RiemannHypothesis` da Mathlib, fixado no repositório do enunciado). Ele
**não** é `∀ ρ, ζ ρ = 0 → Re ρ = ½`: esse enunciado é falso por causa dos zeros triviais (`clay_como_proposto_falso`).

Os dois caminhos ficam como implicações provadas no kernel: se as peças que faltam forem provadas, o alvo fecha.

* `target_de_li`: `CriterioDeLi` (verdadeiro, não formalizado) + `PositividadeDeLi` (aberto) ⟹ `Target`.
* `target_de_dbn`: `RH_iff_Lambda` (verdadeiro, não formalizado) + `Λ ≤ 0` (aberto) ⟹ `Target`.

Nenhum `sorry`, nenhum `axiom`: as hipóteses abertas estão nos argumentos, à vista. `Main.lean` continua sem `main`
e `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Fronteira

/-- O alvo como foi proposto, `∀ ρ, ζ ρ = 0 → Re ρ = ½`, é falso: `ζ(−2) = 0` e `Re(−2) = −2`. -/
theorem clay_como_proposto_falso : ¬ ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re = 1 / 2 := by
  intro h
  have h0 := h _ (riemannZeta_neg_two_mul_nat_add_one 0)
  norm_num at h0

/-- Caminho 1: o critério de Li e a positividade fecham o alvo. -/
theorem target_de_li (hLi : CriterioDeLi) (hPos : PositividadeDeLi) : Target := hLi.mpr hPos

/-- Caminho 2: de Bruijn–Newman com `Λ ≤ 0` fecha o alvo. -/
theorem target_de_dbn (h : RH_iff_Lambda) (hΛ : deBruijnNewman ≤ 0) : Target := h.mpr hΛ

end ClayRiemannProof.Fronteira
