import ClayRiemannProof.EixoRiemann.Tres
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Valores, par e ímpar, e o que é chão firme

## Lógica
* `lukasiewicz_fixo_iff`, `lukasiewicz_fixo_unico`: em Łukasiewicz com `m + 1` valores `{0, 1/m, …, 1}`, a negação
  `x ↦ 1 − x` tem ponto fixo ⟺ `m` é par (número de valores **ímpar**), e o fixo é único: `1/2`.
  `lukasiewicz_continuo_fixo`: em `[0, 1]`, o único fixo é `1/2`. Esta é a versão verdadeira de "par/ímpar" na lógica.
* `V4` (Belnap): `F, N (nem), B (ambos), T`. `belnap_dois_fixos`: a negação fixa exatamente `N` e `B`.
  `belnap_de_morgan`, `belnap_dupla_negacao`, `belnap_assoc`, `belnap_distributiva`: é um reticulado de De Morgan.
  `belnap_estende_kleene`: `{F, N, T}` é o Kleene de `Tres`, fechado. `belnap_sem_explosao`: com designados `{T, B}`,
  contradição não implica tudo.
* `e5_nao_associativo`: a extensão para 5 valores proposta (`2 ∧ 3 = 0` e `4` absorvente) **não é associativa**:
  `(2 ∧ 3) ∧ 4 = 0`, `2 ∧ (3 ∧ 4) = 4`. As escadas de 5, 6, …, 11 valores herdam o problema.

## ζ: par e ímpar
* `zeta_par_fecha`: `ζ(2k) = q·π^{2k}` com `q ∈ ℚ` (Euler).
* `cos_impar_zero`, `equacao_funcional_cega_impar`: em `s = 2k + 1` o fator `cos(πs/2)` da equação funcional é `0`;
  a equação vale para **qualquer** valor de `ζ(2k + 1)`. É por isso que a simetria fecha os pares e não diz nada dos
  ímpares.

## Cauda
* `cauda_primos_iff`: `Σ_p p^{−σ}` converge ⟺ `σ > 1`. `cauda_meio_diverge`: em `σ = 1/2` diverge.

## Simetrias (parte linear)
* `tensao_parte_linear`: `s ↦ 1 − s` tem parte linear `−id` (em `(σ, t)`: `diag(−1, −1)`, det `1`), fixa só `1/2`
  (`tensao_fixo_iff`). `torcao_parte_linear`: `s ↦ 1 − s̄` tem parte linear `−conj` (`diag(−1, 1)`, det `−1`), fixa a
  reta inteira (`torcao_fixo_iff`). O eixo é o fixo da **torção**, não da tensão.
-/

open ClayRiemannProof.Zeta.Symmetry

namespace EixoRiemann.Valores

/-! ## Łukasiewicz finito e contínuo -/

theorem lukasiewicz_fixo_iff (m : ℕ) : (∃ k, k ≤ m ∧ m - k = k) ↔ Even m := by
  constructor
  · rintro ⟨k, -, h⟩
    exact ⟨k, by omega⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, by omega, by omega⟩

theorem lukasiewicz_fixo_unico {m k l : ℕ} (hk : k ≤ m) (hl : l ≤ m) (h1 : m - k = k) (h2 : m - l = l) :
    k = l := by
  omega

theorem lukasiewicz_continuo_fixo (x : ℝ) : 1 - x = x ↔ x = 1 / 2 := by
  constructor <;> intro h <;> linarith

/-! ## Belnap -/

inductive V4
  | F
  | N
  | B
  | T
  deriving DecidableEq, Repr

open V4

instance : Fintype V4 where
  elems := {F, N, B, T}
  complete := fun x => by cases x <;> decide

def nao4 : V4 → V4
  | F => T
  | T => F
  | N => N
  | B => B

def e4 : V4 → V4 → V4
  | F, _ => F
  | _, F => F
  | T, y => y
  | x, T => x
  | N, N => N
  | B, B => B
  | N, B => F
  | B, N => F

def ou4 : V4 → V4 → V4
  | T, _ => T
  | _, T => T
  | F, y => y
  | x, F => x
  | N, N => N
  | B, B => B
  | N, B => T
  | B, N => T

def designado (x : V4) : Prop := x = T ∨ x = B

instance : DecidablePred designado := fun x => by unfold designado; infer_instance

theorem belnap_dois_fixos : ∀ x : V4, nao4 x = x ↔ x = N ∨ x = B := by decide

theorem belnap_dupla_negacao : ∀ x : V4, nao4 (nao4 x) = x := by decide

theorem belnap_de_morgan : ∀ x y : V4, nao4 (e4 x y) = ou4 (nao4 x) (nao4 y) := by decide

theorem belnap_assoc : ∀ x y z : V4, e4 (e4 x y) z = e4 x (e4 y z) := by decide

theorem belnap_distributiva : ∀ x y z : V4, e4 x (ou4 y z) = ou4 (e4 x y) (e4 x z) := by decide

theorem belnap_nem_ambos : e4 N B = F ∧ ou4 N B = T := by decide

/-- `{F, N, T}` dentro de Belnap é o Kleene de `Tres`. -/
def deTres : Tres.V3 → V4
  | .F => F
  | .U => N
  | .T => T

theorem belnap_estende_kleene :
    (∀ x y, deTres (Tres.e x y) = e4 (deTres x) (deTres y)) ∧
      (∀ x y, deTres (Tres.ou x y) = ou4 (deTres x) (deTres y)) ∧
      (∀ x, deTres (Tres.nao x) = nao4 (deTres x)) := by
  decide

/-- Com designados `{T, B}`: `B ∧ ¬B` é designado e `F` não; contradição não implica tudo. -/
theorem belnap_sem_explosao : designado (e4 B (nao4 B)) ∧ ¬ designado F := by decide

/-! ## A escada de 5 valores proposta -/

/-- `∧` da extensão para 5 valores proposta: `0` domina, `1` é neutro, `2 ∧ 3 = 0` (Belnap), `4` absorve `2, 3`. -/
def e5 (x y : Fin 5) : Fin 5 :=
  if x = 0 ∨ y = 0 then 0
  else if x = 1 then y
  else if y = 1 then x
  else if x = y then x
  else if (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2) then 0
  else 4

theorem e5_nao_associativo : e5 (e5 2 3) 4 ≠ e5 2 (e5 3 4) := by decide

/-! ## ζ: par fecha, ímpar abre -/

theorem zeta_par_fecha {k : ℕ} (hk : k ≠ 0) :
    ∃ q : ℚ, riemannZeta (2 * k) = (q : ℂ) * (Real.pi : ℂ) ^ (2 * k) := by
  refine ⟨(-1) ^ (k + 1) * 2 ^ (2 * k - 1) * bernoulli (2 * k) / (2 * k).factorial, ?_⟩
  rw [riemannZeta_two_mul_nat hk]
  push_cast
  ring

theorem cos_impar_zero (k : ℕ) : Complex.cos (Real.pi * (2 * k + 1) / 2) = 0 := by
  rw [Complex.cos_eq_zero_iff]
  exact ⟨(k : ℤ), by push_cast; ring⟩

/-- Em `s = 2k + 1`, o lado direito da equação funcional `2(2π)^{−s} Γ(s) cos(πs/2) ζ(s)` é `0` para qualquer
valor `z` no lugar de `ζ(s)`. -/
theorem equacao_funcional_cega_impar (k : ℕ) (z : ℂ) :
    2 * (2 * Real.pi) ^ (-(2 * k + 1 : ℂ)) * Complex.Gamma (2 * k + 1) *
      Complex.cos (Real.pi * (2 * k + 1) / 2) * z = 0 := by
  rw [cos_impar_zero]
  ring

/-! ## Cauda -/

theorem cauda_primos_iff (σ : ℝ) : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-σ)) ↔ 1 < σ := by
  rw [Nat.Primes.summable_rpow]
  constructor <;> intro h <;> linarith

theorem cauda_meio_diverge : ¬ Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(1 / 2 : ℝ))) := by
  rw [cauda_primos_iff]
  norm_num

/-! ## Simetrias: parte linear -/

theorem tensao_parte_linear (a b : ℂ) : tensao a - tensao b = -(a - b) := by
  unfold tensao
  ring

theorem torcao_parte_linear (a b : ℂ) : torcao a - torcao b = -(starRingEnd ℂ) (a - b) := by
  unfold torcao
  rw [map_sub]
  ring

end EixoRiemann.Valores

#print axioms EixoRiemann.Valores.lukasiewicz_fixo_iff
#print axioms EixoRiemann.Valores.lukasiewicz_fixo_unico
#print axioms EixoRiemann.Valores.lukasiewicz_continuo_fixo
#print axioms EixoRiemann.Valores.belnap_dois_fixos
#print axioms EixoRiemann.Valores.belnap_de_morgan
#print axioms EixoRiemann.Valores.belnap_assoc
#print axioms EixoRiemann.Valores.belnap_distributiva
#print axioms EixoRiemann.Valores.belnap_estende_kleene
#print axioms EixoRiemann.Valores.belnap_sem_explosao
#print axioms EixoRiemann.Valores.e5_nao_associativo
#print axioms EixoRiemann.Valores.zeta_par_fecha
#print axioms EixoRiemann.Valores.cos_impar_zero
#print axioms EixoRiemann.Valores.equacao_funcional_cega_impar
#print axioms EixoRiemann.Valores.cauda_primos_iff
#print axioms EixoRiemann.Valores.cauda_meio_diverge
#print axioms EixoRiemann.Valores.tensao_parte_linear
#print axioms EixoRiemann.Valores.torcao_parte_linear
