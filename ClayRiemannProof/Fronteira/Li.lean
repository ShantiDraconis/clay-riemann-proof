import ClayRiemannProof.Fronteira.Hadamard

/-!
# Caminho 1: positividade (critério de Li)

`λₙ = 1/(n − 1)! · dⁿ/dsⁿ [s^{n−1} log ξ(s)]` em `s = 1` (Li 1997). Com o produto de Hadamard isso vira
`λₙ = Σ_ρ [1 − (1 − 1/ρ)ⁿ]` (zeros com multiplicidade, somados em pares `ρ, 1 − ρ`), e Bombieri–Lagarias (1999) dão a
forma aritmética (soma sobre primos + termos de Γ). **Critério de Li**: RH ⟺ `λₙ ≥ 0` para todo `n ≥ 1`.

Aqui `liCoeff` é a definição de Li (derivadas de `log ξ` em 1, onde `ξ(1) = ½`), e `CriterioDeLi`,
`PositividadeDeLi` são enunciados (`Prop`): o primeiro é verdadeiro e não formalizado (precisa de `XiHadamard` e da
fórmula explícita); o segundo é RH por outro nome — aberto. Foi a positividade (Weil) que fechou o análogo para curvas
sobre corpos finitos; para ζ ninguém sabe provar.
-/

noncomputable section

namespace ClayRiemannProof.Fronteira

open Complex

/-- Coeficientes de Li: `λₙ = 1/(n − 1)! · dⁿ/dsⁿ [s^{n−1} log ξ(s)]|_{s=1}`. -/
def liCoeff (n : ℕ) : ℂ :=
  iteratedDeriv n (fun s => s ^ (n - 1) * log (xi s)) 1 / ((n - 1).factorial : ℂ)

/-- **Critério de Li** (Li 1997; Bombieri–Lagarias 1999) — enunciado, verdadeiro, não formalizado. -/
def CriterioDeLi : Prop := RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → 0 ≤ (liCoeff n).re

/-- A positividade que fecharia RH por este caminho — aberta. -/
def PositividadeDeLi : Prop := ∀ n : ℕ, 1 ≤ n → 0 ≤ (liCoeff n).re

end ClayRiemannProof.Fronteira
