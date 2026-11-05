import ClayRiemannProof.TresEstados

/-!
# As provas condicionais da proporção na reta

O método de 2026 (Lamzouri, Prop. 2.1 e Lema 3.2) tem duas entradas analíticas que ainda não estão no kernel: a
desigualdade de Bessel `N₀ˢ ≥ 2N − S` e a cota de correlação de pares `S ≤ (C + ε)N`. Aqui elas entram como hipóteses
nomeadas (`EntradasLamzouri`), junto com as duas comparações entre as contagens da literatura (com multiplicidade,
zeros simples) e as do kernel (sem multiplicidade). O kernel prova o resto:

* `proporcao_de_entradas`: as entradas com a constante `C` dão `ProporcaoNaReta Z (2 − C)`.
* `proporcao_2026`: com `C = C_MT = ½ + (1/√2)·cot(1/√2)` (`Lamzouri2026`, hipótese nomeada), `2 − C_MT ≈ 0,6725`.
* `proporcao_de_cp`: com a correlação de pares até o alcance `A` e a densidade uniforme (`CorrelacaoAte A`, hipótese
  nomeada; conjectura para `A > 1`), a fração é `≥ 1 − 1/(3A²)`.
* `cp_implica_cem`: com a correlação de pares em todo alcance, a fração é 100% (`ProporcaoNaReta Z 1`). É a forma
  condicional do resultado de Goldston, Lee, Schettler e Suriajaya.

100% continua não sendo a RH (`Proporcao.cem_por_cento_nao_basta`). Nada aqui prova RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Condicionais

open Filter Topology ClayRiemannProof.Zeta.Symmetry ClayRiemannProof.Proporcao

/-- **As entradas do método de 2026**, como hipóteses nomeadas sobre as contagens da literatura: `Ns` (zeros simples
na reta), `Nm` (todos, com multiplicidade) e a soma de pares `S = Σ K(γ − γ')²`. -/
structure EntradasLamzouri (Ns Nm S : ℝ → ℝ) (C : ℝ) : Prop where
  /-- Os simples na reta são no máximo os distintos na reta. -/
  simples_na_reta : ∀ᶠ T in atTop, Ns T ≤ N0 Z T
  /-- Os distintos são no máximo os contados com multiplicidade. -/
  com_multiplicidade : ∀ᶠ T in atTop, (N Z T : ℝ) ≤ Nm T
  /-- A desigualdade de Bessel (Lamzouri, Prop. 2.1). -/
  bessel : ∀ᶠ T in atTop, 2 * Nm T - S T ≤ Ns T
  /-- A correlação de pares, que dá a constante `C`. -/
  correlacao : ∀ ε > 0, ∀ᶠ T in atTop, S T ≤ (C + ε) * Nm T

/-- **As entradas com a constante `C` dão a fração `2 − C` na reta.** -/
theorem proporcao_de_entradas {Ns Nm S : ℝ → ℝ} {C : ℝ} (h : EntradasLamzouri Ns Nm S C) :
    ProporcaoNaReta Z (2 - C) := by
  intro ε hε
  have hb : ∀ᶠ T in atTop, 0 < Nm T := by
    filter_upwards [N_Z_pos, h.com_multiplicidade] with T h1 h2
    have : (0 : ℝ) < N Z T := by exact_mod_cast Nat.pos_of_ne_zero h1
    linarith
  have hesq := esqueleto h.bessel h.correlacao hb ε hε
  filter_upwards [hesq, h.simples_na_reta, h.com_multiplicidade, N_Z_pos] with T h1 h2 h3 h4
  have hN : (0 : ℝ) < N Z T := by exact_mod_cast Nat.pos_of_ne_zero h4
  unfold proporcao
  by_cases hc : 2 - C - ε ≤ 0
  · exact hc.trans (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · have hc' : 0 < 2 - C - ε := lt_of_not_ge hc
    have hNm : 0 < Nm T := lt_of_lt_of_le hN h3
    have hNs : 0 < Ns T := by
      have h5 : 0 < Ns T / Nm T := lt_of_lt_of_le hc' h1
      exact (div_pos_iff_of_pos_right hNm).mp h5
    calc 2 - C - ε ≤ Ns T / Nm T := h1
      _ ≤ Ns T / N Z T := div_le_div_of_nonneg_left hNs.le hN h3
      _ ≤ N0 Z T / N Z T := div_le_div_of_nonneg_right h2 hN.le

/-- A constante de Montgomery–Taylor, `½ + (1/√2)·cot(1/√2) ≈ 1,3275`. -/
noncomputable def C_MT : ℝ := 1 / 2 + (1 / Real.sqrt 2) * (Real.cos (1 / Real.sqrt 2) / Real.sin (1 / Real.sqrt 2))

/-- **Lamzouri (2026)**, como hipótese nomeada: as entradas valem com `C = C_MT`. -/
def Lamzouri2026 : Prop := ∃ Ns Nm S : ℝ → ℝ, EntradasLamzouri Ns Nm S C_MT

/-- **O resultado de 2026, condicional às entradas**: a fração na reta é `≥ 2 − C_MT ≈ 0,6725`. -/
theorem proporcao_2026 (h : Lamzouri2026) : ProporcaoNaReta Z (2 - C_MT) := by
  obtain ⟨Ns, Nm, S, hE⟩ := h
  exact proporcao_de_entradas hE

/-- **CP(A)**, como hipótese nomeada: as entradas valem com a constante da densidade uniforme em `[−A/2, A/2]`,
`C = 1 + 1/(3A²)`. Para `A = 1` isto é o teorema de Montgomery; para `A > 1` é a conjectura de correlação de pares
até o alcance `A`. -/
def CorrelacaoAte (A : ℝ) : Prop := ∃ Ns Nm S : ℝ → ℝ, EntradasLamzouri Ns Nm S (1 + 1 / (3 * A ^ 2))

/-- **CP(A) dá a fração `1 − 1/(3A²)`**: 2/3 com `A = 1`, 11/12 com `A = 2`. -/
theorem proporcao_de_cp {A : ℝ} (h : CorrelacaoAte A) : ProporcaoNaReta Z (1 - 1 / (3 * A ^ 2)) := by
  obtain ⟨Ns, Nm, S, hE⟩ := h
  have := proporcao_de_entradas hE
  convert this using 1
  ring

/-- **A correlação de pares em todo alcance dá 100%**: se CP(A) vale para todo `A ≥ 1`, então
`ProporcaoNaReta Z 1`. -/
theorem cp_implica_cem (h : ∀ A : ℝ, 1 ≤ A → CorrelacaoAte A) : ProporcaoNaReta Z 1 := by
  intro ε hε
  set A : ℝ := 1 + 1 / ε with hA
  have hi : 0 < 1 / ε := by positivity
  have hA1 : 1 ≤ A := by linarith
  have h1 : 1 ≤ ε * A := by
    rw [hA, mul_add, mul_one_div_cancel hε.ne']
    linarith
  have hbound : 1 / (3 * A ^ 2) ≤ ε / 3 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [mul_le_mul h1 hA1 zero_le_one (by positivity : (0 : ℝ) ≤ ε * A)]
  filter_upwards [proporcao_de_cp (h A hA1) (ε / 2) (by positivity)] with T hT
  linarith

end ClayRiemannProof.Condicionais
