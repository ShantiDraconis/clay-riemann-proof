import ClayRiemannProof.EixoRiemann.Tres
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.Nonvanishing

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

/-! ## A reta em `1/x`

O `1/2` não é parâmetro: zeros vêm em pares `ρ`, `1 − ρ̄` (mesma altura, partes reais `β` e `1 − β`).
* `reta_unica`, `hardy_reta_unica`: se todo zero estivesse numa reta `Re = c`, então `c = 1/2`.
* `faixa_simetrica`: "todo zero tem `Re ≤ θ`" ⟺ "todo zero está a distância `≤ θ − 1/2` da reta".
* `abaixo_do_meio_falso`: para `θ < 1/2` (`1/x` com `x > 2`), "todo zero tem `Re ≤ θ`" é falso.
* `quase_rh_iff_pontes`: para `1/2 ≤ θ < 1` (`1 < x ≤ 2`), "todo zero tem `Re ≤ θ`" ⟺ toda ponte horizontal tem
  `|δ| ≤ 2θ − 1`. Em `θ = 1/2` é RH; em `1/2 < θ < 1` é a quase-RH, aberta para todo `θ`.
* `acima_de_um_trivial`: para `θ ≥ 1` (`x ≤ 1`) é verdade sem hipótese. -/

theorem reta_unica {c : ℝ} (hZ : Z.Nonempty) (h : ∀ ρ ∈ Z, ρ.re = c) : c = 1 / 2 := by
  obtain ⟨ρ, hρ⟩ := hZ
  have a := h ρ hρ
  have b := h _ (torcao_mem_Z hρ)
  rw [re_torcao] at b
  linarith

theorem hardy_reta_unica (hH : Hardy1914) {c : ℝ} (h : ∀ ρ ∈ Z, ρ.re = c) : c = 1 / 2 :=
  reta_unica (Z_nonempty_de_hardy hH) h

theorem faixa_simetrica (θ : ℝ) :
    (∀ ρ ∈ Z, ρ.re ≤ θ) ↔ ∀ ρ ∈ Z, |ρ.re - 1 / 2| ≤ θ - 1 / 2 := by
  constructor
  · intro h ρ hρ
    have a := h ρ hρ
    have b := h _ (torcao_mem_Z hρ)
    rw [re_torcao] at b
    rw [abs_le]
    constructor <;> linarith
  · intro h ρ hρ
    have h1 := h ρ hρ
    have h2 := le_abs_self (ρ.re - 1 / 2)
    linarith

theorem abaixo_do_meio_falso {θ : ℝ} (hθ : θ < 1 / 2) (hZ : Z.Nonempty) : ¬ ∀ ρ ∈ Z, ρ.re ≤ θ := by
  intro h
  obtain ⟨ρ, hρ⟩ := hZ
  have h1 := (faixa_simetrica θ).mp h ρ hρ
  have h2 := abs_nonneg (ρ.re - 1 / 2)
  linarith

theorem quase_rh_iff_pontes (θ : ℝ) :
    (∀ ρ ∈ Z, ρ.re ≤ θ) ↔ ∀ (s : ℂ) (r : ℝ), s ∈ Z → s + (r : ℂ) ∈ Z → |r| ≤ 2 * θ - 1 := by
  rw [faixa_simetrica]
  constructor
  · intro h s r hs hsr
    have a := h s hs
    have b := h _ hsr
    rw [Complex.add_re, Complex.ofReal_re] at b
    rw [abs_le] at a b ⊢
    constructor <;> linarith [a.1, a.2, b.1, b.2]
  · intro h ρ hρ
    have hb := h ρ (1 - 2 * ρ.re) hρ (by rw [soma_real_eq_torcao]; exact torcao_mem_Z hρ)
    rw [abs_le] at hb ⊢
    constructor <;> linarith [hb.1, hb.2]

theorem acima_de_um_trivial : ∀ ρ ∈ Z, ρ.re ≤ 1 := fun ρ hρ => by
  obtain ⟨-, -, h1⟩ := hρ
  exact h1.le

/-! ## A lei irredutível e por que ela sozinha não resolve

A lei irredutível é a simetria de Klein: `f(1 − s) = f(s)` e `f(s̄) = conj f(s)`. Ela dá o eixo (fixo da torção), os
quartetos e o piso `θ ≥ 1/2`. Mas um conjunto invariante pode conter órbitas de 4 pontos fora da reta. `contraQ` tem
exatamente as mesmas simetrias de ζ e um quarteto de zeros fora da reta (`3/5 ± i`, `2/5 ± i`). Logo nenhum argumento
que use só a simetria pode provar RH (`simetria_nao_implica_reta`). Na literatura, o mesmo vale para uma função com a
própria equação funcional de ζ (Davenport–Heilbronn), que tem zeros fora da reta e não tem produto de Euler. -/

noncomputable def contraQ (s : ℂ) : ℂ := ((s - 3 / 5) ^ 2 + 1) * ((s - 2 / 5) ^ 2 + 1)

theorem contraQ_tensao (s : ℂ) : contraQ (1 - s) = contraQ s := by
  unfold contraQ
  ring

theorem contraQ_espelho (s : ℂ) : contraQ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (contraQ s) := by
  unfold contraQ
  simp [map_add, map_mul, map_sub, map_pow, map_div₀, map_ofNat, map_one]

theorem contraQ_zero : contraQ (3 / 5 + Complex.I) = 0 := by
  unfold contraQ
  have h : (3 / 5 + Complex.I - 3 / 5 : ℂ) = Complex.I := by ring
  rw [h, Complex.I_sq]
  ring

/-- **A simetria sozinha não decide**: existe função com as simetrias de ζ e um zero fora da reta. -/
theorem simetria_nao_implica_reta :
    ¬ ∀ f : ℂ → ℂ, (∀ s, f (1 - s) = f s) → (∀ s, f ((starRingEnd ℂ) s) = (starRingEnd ℂ) (f s)) →
      ∀ ρ, f ρ = 0 → ρ.re = 1 / 2 := by
  intro h
  have h' := h contraQ contraQ_tensao contraQ_espelho _ contraQ_zero
  norm_num at h'

/-! ## O uso dos primos que a simetria não tem

`positividade_dos_primos`: para `x > 0`, `‖ζ(1+x)³ ζ(1+x+iy)⁴ ζ(1+x+2iy)‖ ≥ 1`. Vem do produto de Euler: `log ζ` é uma
série de Dirichlet com coeficientes `Λ(n)/log n ≥ 0`, combinada com `3 + 4 cos θ + cos 2θ ≥ 0`. É o que exclui zeros em
`Re s = 1`. `contraQ` e Davenport–Heilbronn não têm produto de Euler; a simetria não dá essa desigualdade. -/

theorem positividade_dos_primos {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖riemannZeta (1 + x) ^ 3 * riemannZeta (1 + x + Complex.I * y) ^ 4 *
      riemannZeta (1 + x + 2 * Complex.I * y)‖ ≥ 1 := by
  have h := DirichletCharacter.norm_LFunction_product_ge_one (N := 1) (1 : DirichletCharacter ℂ 1) hx y
  simpa [DirichletCharacter.LFunctionTrivChar] using h

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
#print axioms EixoRiemann.Valores.reta_unica
#print axioms EixoRiemann.Valores.hardy_reta_unica
#print axioms EixoRiemann.Valores.faixa_simetrica
#print axioms EixoRiemann.Valores.abaixo_do_meio_falso
#print axioms EixoRiemann.Valores.quase_rh_iff_pontes
#print axioms EixoRiemann.Valores.acima_de_um_trivial
#print axioms EixoRiemann.Valores.contraQ_tensao
#print axioms EixoRiemann.Valores.contraQ_espelho
#print axioms EixoRiemann.Valores.contraQ_zero
#print axioms EixoRiemann.Valores.simetria_nao_implica_reta
#print axioms EixoRiemann.Valores.positividade_dos_primos
