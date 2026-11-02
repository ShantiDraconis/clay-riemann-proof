import ClayRiemannProof.Fronteira.Hadamard

/-!
# Caminho 2: deformação (de Bruijn–Newman)

`Φ(u) = Σ_{n≥1} (2π²n⁴e^{9u} − 3πn²e^{5u}) e^{−πn²e^{4u}}` e `H_t(z) = ∫₀^∞ e^{tu²} Φ(u) cos(zu) du`.
`H₀(z) = ξ(½ + iz/2)/8` (Riemann/Pólya), de Bruijn (1950): existe `Λ` tal que `H_t` só tem zeros reais exatamente para
`t ≥ Λ`; RH ⟺ `Λ ≤ 0`. Rodgers–Tao (2018): `Λ ≥ 0`. Polymath 15 / Platt–Trudgian (2021): `Λ ≤ 0,2`.
Logo RH ⟺ `Λ = 0`, e fechar isso pede uma estimativa uniforme em `t`, não uma conta finita.

Aqui `Phi`, `H` e `deBruijnNewman` são definições de verdade; `H0_eh_xi`, `RodgersTao`, `RH_iff_Lambda` e
`PlattTrudgianLambda` são enunciados (`Prop`) de teoremas publicados, não formalizados.
-/

noncomputable section

namespace ClayRiemannProof.Fronteira

open Complex MeasureTheory

/-- `Φ(u) = Σ_{n≥1} (2π²n⁴e^{9u} − 3πn²e^{5u}) e^{−πn²e^{4u}}`. -/
def Phi (u : ℝ) : ℝ :=
  ∑' n : ℕ, (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u)
      - 3 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * u)) * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (4 * u))

/-- `H_t(z) = ∫₀^∞ e^{tu²} Φ(u) cos(zu) du`. -/
def H (t : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Set.Ioi (0 : ℝ), ((Real.exp (t * u ^ 2) * Phi u : ℝ) : ℂ) * Complex.cos (z * u)

/-- A constante de de Bruijn–Newman: `Λ = inf {t | todos os zeros de H_t são reais}`. -/
def deBruijnNewman : ℝ := sInf {t : ℝ | ∀ z : ℂ, H t z = 0 → z.im = 0}

/-- `H₀(z) = ξ(½ + iz/2)/8` — enunciado. -/
def H0_eh_xi : Prop := ∀ z : ℂ, H 0 z = xi (1 / 2 + I * z / 2) / 8

/-- Rodgers–Tao (2018): `Λ ≥ 0` — enunciado. -/
def RodgersTao : Prop := 0 ≤ deBruijnNewman

/-- de Bruijn (1950) + Newman (1976): RH ⟺ `Λ ≤ 0` — enunciado. -/
def RH_iff_Lambda : Prop := RiemannHypothesis ↔ deBruijnNewman ≤ 0

/-- Platt–Trudgian (2021): `Λ ≤ 0,2` — enunciado. -/
def PlattTrudgianLambda : Prop := deBruijnNewman ≤ 0.2

end ClayRiemannProof.Fronteira
