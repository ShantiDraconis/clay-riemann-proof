import Mathlib

/-!
# A peça que trava os outros caminhos: Hadamard para ξ

`ξ(s) = ½ s(s − 1) π^{−s/2} Γ(s/2) ζ(s)` é inteira, de ordem 1, e satisfaz `ξ(1 − s) = ξ(s)`. O teorema de Hadamard
(1893) dá o produto `ξ(s) = e^{A+Bs} ∏_ρ (1 − s/ρ) e^{s/ρ}` sobre os zeros não triviais. Ele é verdadeiro e é a base
do critério de Li e da teoria de de Bruijn–Newman, mas **não está na Mathlib**.

Aqui:

* `xi`: a função ξ, escrita com a parte inteira `Λ₀ = completedRiemannZeta₀` da Mathlib,
  `ξ(s) = (s(s − 1)Λ₀(s) + 1)/2` — os polos de `Λ` em 0 e 1 se cancelam, sem valor convencional;
* provados no kernel: `xi_one_sub` (a ponte), `differentiable_xi` (inteira), `xi_zero`, `xi_one`, `xi_eq`
  (fora de 0 e 1, `ξ = ½ s(s − 1)Λ`);
* `XiHadamard`: o enunciado do produto de Hadamard, como `Prop`. **Não é teorema aqui** — é o próximo buraco a
  formalizar. Nenhum `sorry`, nenhum `axiom`: o enunciado fica registrado e nada depende dele sem dizer.
-/

noncomputable section

namespace ClayRiemannProof.Fronteira

open Complex

/-- `ξ(s) = ½ s(s − 1) π^{−s/2} Γ(s/2) ζ(s) = (s(s − 1)Λ₀(s) + 1)/2`. -/
def xi (s : ℂ) : ℂ := (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- A ponte `ξ(1 − s) = ξ(s)`. -/
theorem xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
  unfold xi
  rw [completedRiemannZeta₀_one_sub]
  ring

/-- `ξ` é inteira. -/
theorem differentiable_xi : Differentiable ℂ xi := by
  have h := differentiable_completedZeta₀
  unfold xi
  fun_prop

theorem xi_zero : xi 0 = 1 / 2 := by simp [xi]

theorem xi_one : xi 1 = 1 / 2 := by simp [xi]

/-- Fora de 0 e 1, `ξ(s) = ½ s(s − 1) Λ(s)` com a completada `Λ = completedRiemannZeta` da Mathlib. -/
theorem xi_eq (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xi s = s * (s - 1) / 2 * completedRiemannZeta s := by
  have h1' : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  rw [completedRiemannZeta_eq]
  unfold xi
  field_simp
  ring

/-- **Hadamard para ξ** (enunciado; verdadeiro, não formalizado na Mathlib): existem `A, B` e uma enumeração `ρ`
dos zeros de `ξ` (todos eles) tais que, para todo `s`, o produto de Weierstrass converge e
`ξ(s) = e^{A+Bs} ∏ₙ (1 − s/ρₙ) e^{s/ρₙ}`. -/
def XiHadamard : Prop :=
  ∃ A B : ℂ, ∃ ρ : ℕ → ℂ, (∀ n, xi (ρ n) = 0) ∧ (∀ z, xi z = 0 → ∃ n, ρ n = z) ∧
    ∀ s, Multipliable (fun n => (1 - s / ρ n) * exp (s / ρ n)) ∧
      xi s = exp (A + B * s) * ∏' n, (1 - s / ρ n) * exp (s / ρ n)

end ClayRiemannProof.Fronteira
