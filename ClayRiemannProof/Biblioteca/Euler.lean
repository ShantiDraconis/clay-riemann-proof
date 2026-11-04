import ClayRiemannProof.Absorcao

/-!
# A ponte Euler–Riemann: o que vale e onde o ½ entra

Provado (Mathlib e `Absorcao`):

* `produto_de_euler`: `ζ(s) = ∏_p (1 − p^{−s})^{−1}` para `Re s > 1`;
* `sem_zeros_re_ge_um`: `ζ(s) ≠ 0` para `Re s ≥ 1` (a reta `Re s = 1` incluída: é o teorema dos números primos);
* `soma_primos_sse`, `soma_quadrados_primos_sse`: `Σ_p p^{−σ}` converge sse `σ > 1`; `Σ_p p^{−2σ}` converge sse
  `σ > ½`;
* `euler_em_meio_diverge`: em `σ = ½` a soma `Σ_p p^{−1/2}` diverge, e o produto não converge.

O ½ é a fronteira da soma dos quadrados (a variância de `log ζ` no modelo aleatório de Bohr–Jessen/Selberg), não do
produto. Passar do produto (válido em `Re s > 1`) para os zeros em `0 < Re s < 1` é exatamente o problema aberto:
nenhum teorema aqui faz essa passagem. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Biblioteca

/-- O produto de Euler de ζ, válido para `Re s > 1` (Mathlib). -/
theorem produto_de_euler {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-s))⁻¹) (riemannZeta s) :=
  riemannZeta_eulerProduct_hasProd hs

/-- ζ não se anula em `Re s ≥ 1` (Mathlib). -/
theorem sem_zeros_re_ge_um {s : ℂ} (hs : 1 ≤ s.re) : riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re hs

/-- As três fronteiras de Euler num só enunciado: produto absoluto em `σ > 1`, soma dos quadrados em `σ > ½`, e
divergência em `σ = ½`. -/
theorem fronteiras_de_euler (σ : ℝ) :
    (Summable (fun p : Nat.Primes => (p : ℝ) ^ (-σ)) ↔ 1 < σ) ∧
    (Summable (fun p : Nat.Primes => ((p : ℝ) ^ (-σ)) ^ 2) ↔ 1 / 2 < σ) ∧
    ¬ Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(1 / 2 : ℝ))) :=
  ⟨Absorcao.soma_primos_sse σ, Absorcao.soma_quadrados_primos_sse σ, Absorcao.euler_em_meio_diverge⟩

end ClayRiemannProof.Biblioteca
