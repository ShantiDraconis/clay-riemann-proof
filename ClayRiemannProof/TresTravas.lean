import ClayRiemannProof.Locks

/-!
# As três travas juntas: o que seguram e o que não seguram

A proposta: os zeros de `ζ` ficariam em `Re s = ½` porque `ζ` tem, ao mesmo tempo,

* a **ponte** `ξ(s) = ξ(1 − s)` (equação funcional),
* a **conjugação** `ζ(s̄) = conj ζ(s)`,
* a **trava de Euler**: o produto de Euler dá `ζ(s) ≠ 0` em `Re s ≥ 1`,

e os "quase Riemann" mostrariam que tirar qualquer uma solta um zero da reta (Davenport–Heilbronn sem Euler,
`ζ(s) + ζ(s + 1)` sem a equação funcional, os bicomplexos com divisores de zero). A conclusão proposta:
"precisa das três juntas para segurar ½".

O que fica provado no kernel:

* `zeta_tem_as_tres`: `ζ` (e `Λ`, a completada da Mathlib) tem as três.
* `quarteto`: qualquer função com as três manda um zero `ρ` para `1 − ρ`, `ρ̄` e `1 − ρ̄` — o retângulo vem
  das travas.
* `tres_travas_nao_bastam`: um polinômio, `G(s) = (s − ¼)(s − ¾)`, inteiro, tem as três (e `ℂ` sem divisores de
  zero) e se anula em `¼` e `¾`. **As três juntas não implicam que os zeros estejam em ½.** O retângulo de um
  zero fora da reta é `{¼, ¾}` e não colapsa.
* `travas_independentes`: cada trava pode falhar com as outras duas valendo (`s − ¾`; `(s − 3/2)(s + ½)`; `i(s − ½)`),
  então nenhuma decorre das outras.

O que **não** está aqui, e por quê:

* Davenport–Heilbronn, Epstein com `h > 1` e `ζ(s) + ζ(s + 1)`: são resultados sobre **outras funções**; os zeros
  fora da reta delas são numéricos (fora do kernel) ou teoremas de contagem que a Mathlib não tem. Mostram, cada um,
  que uma propriedade a menos permite zero fora; não mostram que as três bastem.
* O produto de Euler como identidade só vale em `Re s > 1`; na faixa crítica não há "trava `p^{−½}`" que seja
  propriedade de `ζ` (`Locks.trava1_algebra` é álgebra de números reais e não restringe zeros).

Conclusão no kernel: "necessárias" vale no sentido fraco dos exemplos; "suficientes" é falso para as três como
propriedades. O que falta para segurar ½ não é uma quarta trava desse tipo: é a hipótese de Riemann, que continua
aberta (`OPEN_MATH = true`).
-/

namespace ClayRiemannProof.TresTravas

open Complex

/-- As três travas (e ser inteira) como propriedades de uma função `F : ℂ → ℂ`. -/
structure Travas (F : ℂ → ℂ) : Prop where
  inteira : Differentiable ℂ F
  ponte : ∀ s, F (1 - s) = F s
  conjugacao : ∀ s, F (starRingEnd ℂ s) = starRingEnd ℂ (F s)
  euler : ∀ s : ℂ, 1 ≤ s.re → F s ≠ 0

/-- **`ζ` tem as três**: a ponte para a completada `Λ`, a conjugação e a trava de Euler (Mathlib). -/
theorem zeta_tem_as_tres :
    (∀ s, completedRiemannZeta (1 - s) = completedRiemannZeta s) ∧
      (∀ s, riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s)) ∧
      (∀ s : ℂ, 1 ≤ s.re → riemannZeta s ≠ 0) :=
  ⟨completedRiemannZeta_one_sub, riemannZeta_conj, fun _ h => riemannZeta_ne_zero_of_one_le_re h⟩

/-- **O retângulo vem das travas**: com as três, um zero `ρ` traz `1 − ρ`, `ρ̄` e `1 − ρ̄`. -/
theorem quarteto {F : ℂ → ℂ} (hF : Travas F) {ρ : ℂ} (h : F ρ = 0) :
    F (1 - ρ) = 0 ∧ F (starRingEnd ℂ ρ) = 0 ∧ F (1 - starRingEnd ℂ ρ) = 0 := by
  have hc : F (starRingEnd ℂ ρ) = 0 := by rw [hF.conjugacao, h, map_zero]
  exact ⟨by rw [hF.ponte, h], hc, by rw [hF.ponte, hc]⟩

/-- O modelo: `G(s) = (s − ¼)(s − ¾)`, com coeficientes reais. -/
noncomputable def G (s : ℂ) : ℂ := (s - ((1 / 4 : ℝ) : ℂ)) * (s - ((3 / 4 : ℝ) : ℂ))

theorem G_inteira : Differentiable ℂ G := by
  unfold G
  fun_prop

theorem G_ponte (s : ℂ) : G (1 - s) = G s := by
  unfold G
  push_cast
  ring

theorem G_conjugacao (s : ℂ) : G (starRingEnd ℂ s) = starRingEnd ℂ (G s) := by
  simp only [G, map_mul, map_sub, Complex.conj_ofReal]

/-- Um fator `s − a` com `a < 1` real não se anula em `Re s ≥ 1`. -/
theorem fator_ne_zero {a : ℝ} (ha : a < 1) {s : ℂ} (h : 1 ≤ s.re) : s - (a : ℂ) ≠ 0 := by
  intro h0
  have := congrArg Complex.re h0
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at this
  linarith

theorem G_euler {s : ℂ} (h : 1 ≤ s.re) : G s ≠ 0 :=
  mul_ne_zero (fator_ne_zero (by norm_num) h) (fator_ne_zero (by norm_num) h)

theorem G_travas : Travas G := ⟨G_inteira, G_ponte, G_conjugacao, fun _ h => G_euler h⟩

theorem G_zero_quarto : G ((1 / 4 : ℝ) : ℂ) = 0 := by
  simp [G]

theorem G_zero_tres_quartos : G ((3 / 4 : ℝ) : ℂ) = 0 := by
  simp [G]

/-- **As três travas juntas não seguram ½**: uma função inteira com a ponte, a conjugação e a trava de Euler
(e valores em `ℂ`, sem divisores de zero) tem zero em `Re s = ¼`, dentro da faixa e fora da reta. -/
theorem tres_travas_nao_bastam :
    ∃ F : ℂ → ℂ, Travas F ∧ (∀ a b : ℂ, a * b = 0 → a = 0 ∨ b = 0) ∧
      ∃ ρ : ℂ, F ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ρ.re ≠ 1 / 2 := by
  refine ⟨G, G_travas, fun a b => mul_eq_zero.mp, (1 / 4 : ℝ), G_zero_quarto, ?_, ?_, ?_⟩ <;>
    simp only [Complex.ofReal_re] <;> norm_num

/-- O retângulo do zero em `¼` é `{¼, ¾}`: as travas o dobram, não o levam para a reta. -/
theorem retangulo_nao_colapsa :
    G (1 - ((1 / 4 : ℝ) : ℂ)) = 0 ∧ (1 - ((1 / 4 : ℝ) : ℂ)).re = 3 / 4 := by
  refine ⟨(quarteto G_travas G_zero_quarto).1, ?_⟩
  simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  norm_num

/-- **Sem a ponte**: `s − ¾` tem a conjugação e a trava de Euler, e um zero em `¾` sem o par em `¼`. -/
theorem sem_ponte :
    (∀ s, (starRingEnd ℂ s - ((3 / 4 : ℝ) : ℂ)) = starRingEnd ℂ (s - ((3 / 4 : ℝ) : ℂ))) ∧
      (∀ s : ℂ, 1 ≤ s.re → s - ((3 / 4 : ℝ) : ℂ) ≠ 0) ∧
      (((1 / 4 : ℝ) : ℂ) - ((3 / 4 : ℝ) : ℂ) ≠ 0) := by
  refine ⟨fun s => by rw [map_sub, Complex.conj_ofReal], fun s h => fator_ne_zero (by norm_num) h, ?_⟩
  rw [← Complex.ofReal_sub]
  exact_mod_cast (by norm_num : (1 / 4 : ℝ) - 3 / 4 ≠ 0)

/-- O modelo sem Euler: `E(s) = (s − 3/2)(s + ½)`. -/
noncomputable def E (s : ℂ) : ℂ := (s - ((3 / 2 : ℝ) : ℂ)) * (s + ((1 / 2 : ℝ) : ℂ))

/-- **Sem a trava de Euler**: `E` tem a ponte e a conjugação e se anula em `3/2`, onde `Re s ≥ 1`. -/
theorem sem_euler :
    (∀ s, E (1 - s) = E s) ∧ (∀ s, E (starRingEnd ℂ s) = starRingEnd ℂ (E s)) ∧
      E ((3 / 2 : ℝ) : ℂ) = 0 ∧ 1 ≤ (((3 / 2 : ℝ) : ℂ)).re := by
  refine ⟨fun s => by unfold E; push_cast; ring, fun s => by simp only [E, map_mul, map_sub, map_add,
    Complex.conj_ofReal], by simp [E], ?_⟩
  simp only [Complex.ofReal_re]
  norm_num

/-- O modelo sem conjugação: `C(s) = i(s − ½)`. -/
noncomputable def C (s : ℂ) : ℂ := I * (s - ((1 / 2 : ℝ) : ℂ))

/-- **Sem a conjugação**: `C` tem a trava de Euler e satisfaz `C(1 − s) = −C(s)`; a conjugação falha em `0`. -/
theorem sem_conjugacao :
    (∀ s : ℂ, 1 ≤ s.re → C s ≠ 0) ∧ C (starRingEnd ℂ 0) ≠ starRingEnd ℂ (C 0) := by
  refine ⟨fun s h => mul_ne_zero I_ne_zero (fator_ne_zero (by norm_num) h), ?_⟩
  simp only [C, map_zero, zero_sub, map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  intro h
  have := congrArg Complex.im h
  simp at this
  norm_num at this

/-- **As travas são independentes**: cada uma pode falhar com as outras valendo. -/
theorem travas_independentes :
    (∃ F : ℂ → ℂ, (∀ s, F (starRingEnd ℂ s) = starRingEnd ℂ (F s)) ∧ (∀ s : ℂ, 1 ≤ s.re → F s ≠ 0) ∧
        ¬ ∀ s, F (1 - s) = F s) ∧
      (∃ F : ℂ → ℂ, (∀ s, F (1 - s) = F s) ∧ (∀ s, F (starRingEnd ℂ s) = starRingEnd ℂ (F s)) ∧
        ¬ ∀ s : ℂ, 1 ≤ s.re → F s ≠ 0) := by
  refine ⟨⟨fun s => s - ((3 / 4 : ℝ) : ℂ), sem_ponte.1, sem_ponte.2.1, fun h => ?_⟩,
    ⟨E, sem_euler.1, sem_euler.2.1, fun h => h _ sem_euler.2.2.2 sem_euler.2.2.1⟩⟩
  have h0 : (1 - ((1 / 4 : ℝ) : ℂ)) - ((3 / 4 : ℝ) : ℂ) = ((1 / 4 : ℝ) : ℂ) - ((3 / 4 : ℝ) : ℂ) :=
    h ((1 / 4 : ℝ) : ℂ)
  have h1 : (1 : ℂ) - ((1 / 4 : ℝ) : ℂ) - ((3 / 4 : ℝ) : ℂ) = 0 := by push_cast; ring
  rw [h1] at h0
  exact sem_ponte.2.2 h0.symm

end ClayRiemannProof.TresTravas
