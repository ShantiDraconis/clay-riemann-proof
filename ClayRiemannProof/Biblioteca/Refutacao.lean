import Mathlib

/-!
# Refutação indireta: como RH cairia sem achar um zero fora da reta

Três critérios clássicos trocam "um zero com `Re s ≠ ½`" por uma afirmação sobre primos ou sobre a função de Möbius.
Nenhum está no Mathlib; entram como hipóteses nomeadas, como o critério de Li e o de Lagarias.

* **von Koch** (`CriterioDeVonKoch`): RH ⟺ `ψ(x) − x = O(√x·log²x)`, com `ψ(x) = Σ_{n ≤ x} Λ(n)`.
* **Schoenfeld** (`CriterioDeSchoenfeld`, a forma explícita, 1976): RH ⟺ `|ψ(x) − x| < √x·log²x/(8π)` para todo
  `x ≥ 73,2`. É uma afirmação Π₁: **um único `x`** acima da cota refutaria RH (`nao_rh_iff_um_x`).
* **Littlewood** (`CriterioDeLittlewood`): RH ⟺ `M(x) = Σ_{n ≤ x} μ(n) = O(x^{1/2+ε})` para todo `ε > 0`. Aqui não
  basta um `x`: refutar pede `ε > 0` e valores de `|M(x)|/x^{1/2+ε}` sem limite (`refuta_por_mertens`).

A conjectura de Mertens (`|M(x)| ≤ √x` para todo `x`) é mais forte que RH e implicaria RH (`rh_de_mertens`); ela é
falsa (Odlyzko–te Riele, 1985, sem `x` explícito conhecido), e isso **não** refuta RH: a falha de `|M(x)| ≤ √x` não dá
o crescimento `x^{1/2+ε}`.

Conferências numéricas até `x = 10⁸` em `computations/infinito/psi_mertens.py` (fora do kernel). `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Biblioteca

/-- A função de Chebyshev `ψ(x) = Σ_{1 ≤ n ≤ x} Λ(n)`. -/
noncomputable def psiCheb (x : ℝ) : ℝ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n

/-- A função de Mertens `M(x) = Σ_{1 ≤ n ≤ x} μ(n)`. -/
noncomputable def mertens (x : ℝ) : ℤ := ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.moebius n

/-- A cota de Schoenfeld `√x·log²x/(8π)`. -/
noncomputable def cotaSchoenfeld (x : ℝ) : ℝ := Real.sqrt x * Real.log x ^ 2 / (8 * Real.pi)

/-- **von Koch** (hipótese nomeada). -/
def CriterioDeVonKoch : Prop :=
  RiemannHypothesis ↔ ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |psiCheb x - x| ≤ C * (Real.sqrt x * Real.log x ^ 2)

/-- **Schoenfeld**, a forma explícita (hipótese nomeada). -/
def CriterioDeSchoenfeld : Prop :=
  RiemannHypothesis ↔ ∀ x : ℝ, 732 / 10 ≤ x → |psiCheb x - x| < cotaSchoenfeld x

/-- **Littlewood** (hipótese nomeada). -/
def CriterioDeLittlewood : Prop :=
  RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → |(mertens x : ℝ)| ≤ C * x ^ (1 / 2 + ε)

/-- A conjectura de Mertens. -/
def ConjecturaDeMertens : Prop := ∀ x : ℝ, 1 ≤ x → |(mertens x : ℝ)| ≤ Real.sqrt x

/-- **Uma sequência que escapa de toda constante refuta RH** (von Koch). -/
theorem refuta_por_psi (h : CriterioDeVonKoch)
    (hs : ∀ C : ℝ, ∃ x : ℝ, 2 ≤ x ∧ C * (Real.sqrt x * Real.log x ^ 2) < |psiCheb x - x|) :
    ¬ RiemannHypothesis := by
  intro hRH
  obtain ⟨C, hC⟩ := h.mp hRH
  obtain ⟨x, hx, hlt⟩ := hs C
  exact absurd (hC x hx) (not_le.mpr hlt)

/-- **Com a forma explícita, um único `x` basta** (Schoenfeld): RH falsa ⟺ existe `x ≥ 73,2` acima da cota. -/
theorem nao_rh_iff_um_x (h : CriterioDeSchoenfeld) :
    ¬ RiemannHypothesis ↔ ∃ x : ℝ, 732 / 10 ≤ x ∧ cotaSchoenfeld x ≤ |psiCheb x - x| := by
  unfold CriterioDeSchoenfeld at h
  rw [h]
  constructor
  · intro hn
    by_contra hc
    push_neg at hc
    exact hn hc
  · rintro ⟨x, hx, hv⟩ hall
    exact absurd (hall x hx) (not_lt.mpr hv)

/-- **Mertens**: refutar pede `ε > 0` e `|M(x)|` acima de toda constante vezes `x^{1/2+ε}`. -/
theorem refuta_por_mertens (h : CriterioDeLittlewood)
    (hs : ∃ ε : ℝ, 0 < ε ∧ ∀ C : ℝ, ∃ x : ℝ, 1 ≤ x ∧ C * x ^ (1 / 2 + ε) < |(mertens x : ℝ)|) :
    ¬ RiemannHypothesis := by
  intro hRH
  obtain ⟨ε, hε, hC⟩ := hs
  obtain ⟨C, hCb⟩ := h.mp hRH ε hε
  obtain ⟨x, hx, hlt⟩ := hC C
  exact absurd (hCb x hx) (not_le.mpr hlt)

/-- **A conjectura de Mertens implicaria RH** (com Littlewood): `√x ≤ x^{1/2+ε}` para `x ≥ 1`. -/
theorem rh_de_mertens (h : CriterioDeLittlewood) (hM : ConjecturaDeMertens) : RiemannHypothesis := by
  refine h.mpr fun ε hε => ⟨1, fun x hx => ?_⟩
  have h1 : Real.sqrt x ≤ x ^ (1 / 2 + ε) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  calc |(mertens x : ℝ)| ≤ Real.sqrt x := hM x hx
    _ ≤ x ^ (1 / 2 + ε) := h1
    _ = 1 * x ^ (1 / 2 + ε) := (one_mul _).symm

end ClayRiemannProof.Biblioteca
