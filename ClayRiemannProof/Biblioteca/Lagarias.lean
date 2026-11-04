import Mathlib

/-!
# O infinito de RH como uma sequência de contas com inteiros (critério de Lagarias)

Lagarias (2002, a partir de Robin, 1984) provou: RH ⟺ para todo `n ≥ 1`, `σ(n) ≤ H_n + e^{H_n} log H_n`, com igualdade
só em `n = 1` (`σ` é a soma dos divisores, `H_n` o número harmônico). O teorema não está no Mathlib; entra como
hipótese nomeada (`CriterioDeLagarias`), como o critério de Li e `RH ⟺ Λ ≤ 0` em `Fronteira`.

Com ele, o infinito muda de tipo: em vez de todos os pontos de uma região de ℂ, uma sequência de desigualdades, cada
uma uma conta finita (`σ(n)` é uma soma sobre os divisores, `H_n` um racional). Provado aqui:

* `lagarias_um`: `n = 1` é igualdade;
* `nao_rh_iff_inteiro`: RH falsa ⟺ um único inteiro `n` viola a desigualdade (RH é uma afirmação Π₁: um contraexemplo
  é finito e conferível);
* `rh_iff_prefixos`: RH ⟺ todos os prefixos finitos `1 ≤ n ≤ N` valem;
* `corte_existe`: existe `X` tal que conferir `n ≤ X` bastaria — mas só pela lógica clássica: se RH vale, qualquer `X`
  serve; se não vale, o `X` é o contraexemplo. Achar um `X` com prova é resolver RH.

A conferência numérica até `n = 10⁷` está em `computations/infinito/` (fora do kernel). `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Biblioteca

open ArithmeticFunction

/-- **A desigualdade de Lagarias** para `n`: `σ(n) ≤ H_n + e^{H_n} log H_n`. -/
def Lagarias (n : ℕ) : Prop :=
  (σ 1 n : ℝ) ≤ (harmonic n : ℝ) + Real.exp (harmonic n) * Real.log (harmonic n)

/-- **O critério de Lagarias** (Lagarias 2002), como hipótese nomeada. -/
def CriterioDeLagarias : Prop := RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → Lagarias n

/-- Em `n = 1` vale a igualdade: `σ(1) = 1 = H_1 + e·log 1`. -/
theorem lagarias_um : Lagarias 1 := by
  unfold Lagarias
  simp [sigma_one_apply, harmonic]

/-- **Um contraexemplo de RH seria um inteiro.** -/
theorem nao_rh_iff_inteiro (h : CriterioDeLagarias) :
    ¬ RiemannHypothesis ↔ ∃ n : ℕ, 1 ≤ n ∧ ¬ Lagarias n := by
  unfold CriterioDeLagarias at h
  rw [h]
  simp only [not_forall, _root_.not_imp, exists_prop]

/-- **RH é o limite dos prefixos finitos.** -/
theorem rh_iff_prefixos (h : CriterioDeLagarias) :
    RiemannHypothesis ↔ ∀ N : ℕ, ∀ n : ℕ, 1 ≤ n → n ≤ N → Lagarias n := by
  unfold CriterioDeLagarias at h
  rw [h]
  exact ⟨fun H _ n h1 _ => H n h1, fun H n h1 => H n n h1 le_rfl⟩

/-- **O corte finito existe, mas não se sabe qual é**: classicamente há `X` com "conferir `n ≤ X` basta"; a prova não
dá `X`. -/
theorem corte_existe (h : CriterioDeLagarias) :
    ∃ X : ℕ, (∀ n : ℕ, 1 ≤ n → n ≤ X → Lagarias n) → RiemannHypothesis := by
  by_cases hRH : RiemannHypothesis
  · exact ⟨0, fun _ => hRH⟩
  · obtain ⟨n, h1, hn⟩ := (nao_rh_iff_inteiro h).mp hRH
    exact ⟨n, fun hp => absurd (hp n h1 le_rfl) hn⟩

end ClayRiemannProof.Biblioteca
