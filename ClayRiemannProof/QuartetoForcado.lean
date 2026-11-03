import ClayRiemannProof.Analogs
import ClayRiemannProof.Colisao

/-!
# Forçar o zero no quarteto

Para `ζ` o quarteto não pode ser forçado: `ζ` é uma função fixa, e na faixa certificada (README §13) os 41 393 zeros
estão na reta com a contagem fechando. O que se força é a **deformação**: no fluxo do calor de de Bruijn
(`Colisao`), abaixo do tempo de colisão de um par, o par sai da reta, e com as duas simetrias da RH vira o quarteto
`½ ± b ± iγ₀`. Rodgers–Tao (`Λ ≥ 0`) dizem que, para todo `t < 0`, `H_t` tem zeros fora da reta: o quarteto forçado
existe em toda deformação para trás.

* `Q`: um par vizinho em `±iγ₀` (coordenada `w = s − ½`) com o parâmetro `κ`;
* `Q_simetrica`: `Q` tem as simetrias `w ↦ −w`, `w ↦ w̄` (as de `ξ`), logo os zeros vêm em quartetos
  (`quarteto_abstrato`, `Q_quarteto_abstrato`);
* `Q_na_reta`: com `κ ≥ 0`, todos os zeros na reta;
* `Q_quarteto`: com `κ < 0`, o quarteto `±√(−κ) ± iγ₀` é de zeros, fora da reta;
* `quarteto_forcado`: com `κ = (a² + 2t)/4` (o par isolado da `Colisao`), reta ⟺ `t ≥ −a²/2`; abaixo, o quarteto
  nasce com `b = √(2(t* − t))/2`.

Os números do par mais frágil da faixa certificada estão em `computations/lehmer/forca.json` (README §22). Nada aqui
prova ou refuta RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.QuartetoForcado

open Complex ComplexConjugate ClayRiemannProof.Analogs

/-- O modelo de um par vizinho em `±iγ₀` (coordenada `w = s − ½`), com o parâmetro `κ` do fluxo:
`Q(w) = ((w − iγ₀)² + κ)((w + iγ₀)² + κ)`. Para `κ = (a² + 2t)/4` é o par isolado `H2 a t` da `Colisao`
(em `z = 2γ`), junto com o seu espelho em `−iγ₀`. -/
def Q (γ₀ κ : ℝ) (w : ℂ) : ℂ := ((w - I * γ₀) ^ 2 + κ) * ((w + I * γ₀) ^ 2 + κ)

/-- `Q` tem as duas simetrias da RH: `Q(−w) = Q(w)` e `Q(w̄) = conj Q(w)`. -/
theorem Q_simetrica (γ₀ κ : ℝ) : Simetrica (Q γ₀ κ) := by
  refine ⟨fun w => by simp only [Q]; ring, fun w => ?_⟩
  simp only [Q, map_mul, map_add, map_pow, map_sub, conj_I, conj_ofReal]
  ring

/-- `z² = −κ` com `κ ≥ 0` obriga `z` imaginário puro. -/
theorem quadrado_neg_re {z : ℂ} {κ : ℝ} (hκ : 0 ≤ κ) (h : z ^ 2 + κ = 0) : z.re = 0 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, zero_re, zero_im] at hre him
  by_contra hx
  have hy : z.im = 0 := by
    rcases mul_eq_zero.mp (by linarith [him] : z.re * z.im = 0) with h | h
    · exact absurd h hx
    · exact h
  rw [hy] at hre
  have : 0 < z.re * z.re := mul_self_pos.mpr hx
  nlinarith

/-- Com `κ ≥ 0` todos os zeros de `Q` estão na reta (`Re w = 0`, isto é, `Re s = ½`). -/
theorem Q_na_reta {γ₀ κ : ℝ} (hκ : 0 ≤ κ) : ∀ w, Q γ₀ κ w = 0 → w.re = 0 := by
  intro w hw
  rcases mul_eq_zero.mp hw with h | h
  · have := quadrado_neg_re hκ h
    simpa using this
  · have := quadrado_neg_re hκ h
    simpa using this

/-- **O quarteto forçado**: com `κ < 0`, `b = √(−κ)` e os quatro pontos `±b ± iγ₀` são zeros de `Q`, fora da reta. -/
theorem Q_quarteto {γ₀ κ : ℝ} (hκ : κ < 0) :
    Q γ₀ κ (Real.sqrt (-κ) + I * γ₀) = 0 ∧ Q γ₀ κ (-Real.sqrt (-κ) + I * γ₀) = 0 ∧
      Q γ₀ κ (Real.sqrt (-κ) - I * γ₀) = 0 ∧ Q γ₀ κ (-Real.sqrt (-κ) - I * γ₀) = 0 ∧ 0 < Real.sqrt (-κ) := by
  have hb : ((Real.sqrt (-κ) : ℝ) : ℂ) ^ 2 = ((-κ : ℝ) : ℂ) := by rw [← ofReal_pow, Real.sq_sqrt (by linarith)]
  refine ⟨?_, ?_, ?_, ?_, Real.sqrt_pos.mpr (by linarith)⟩ <;> simp only [Q]
  · have : ((Real.sqrt (-κ) : ℂ) + I * γ₀ - I * γ₀) ^ 2 + κ = 0 := by
      rw [add_sub_cancel_right, hb]; push_cast; ring
    rw [this, zero_mul]
  · have : (-(Real.sqrt (-κ) : ℂ) + I * γ₀ - I * γ₀) ^ 2 + κ = 0 := by
      rw [add_sub_cancel_right, neg_sq, hb]; push_cast; ring
    rw [this, zero_mul]
  · have : ((Real.sqrt (-κ) : ℂ) - I * γ₀ + I * γ₀) ^ 2 + κ = 0 := by
      rw [sub_add_cancel, hb]; push_cast; ring
    rw [this, mul_zero]
  · have : (-(Real.sqrt (-κ) : ℂ) - I * γ₀ + I * γ₀) ^ 2 + κ = 0 := by
      rw [sub_add_cancel, neg_sq, hb]; push_cast; ring
    rw [this, mul_zero]

/-- **Forçar o quarteto pelo fluxo**: com `κ = (a² + 2t)/4` (o par isolado da `Colisao`), todos os zeros de `Q`
ficam na reta exatamente para `t ≥ −a²/2`; abaixo disso nasce o quarteto `½ ± b ± iγ₀` com
`b = √(−(a² + 2t))/2 = √(2(t* − t))/2`. -/
theorem quarteto_forcado (a t γ₀ : ℝ) :
    (∀ w, Q γ₀ ((a ^ 2 + 2 * t) / 4) w = 0 → w.re = 0) ↔ -(a ^ 2) / 2 ≤ t := by
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    have hκ : (a ^ 2 + 2 * t) / 4 < 0 := by linarith
    obtain ⟨h1, -, -, -, hb⟩ := Q_quarteto (γ₀ := γ₀) hκ
    have := h _ h1
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] at this
    linarith
  · intro ht
    exact Q_na_reta (by linarith [sq_nonneg a])

/-- O quarteto pela lei abstrata do `Analogs`: um zero de `Q` traz `−w`, `w̄` e `−w̄`. -/
theorem Q_quarteto_abstrato {γ₀ κ : ℝ} {w : ℂ} (h : Q γ₀ κ w = 0) :
    Q γ₀ κ (-w) = 0 ∧ Q γ₀ κ (conj w) = 0 ∧ Q γ₀ κ (-conj w) = 0 :=
  quarteto_abstrato (Q_simetrica γ₀ κ) h

end ClayRiemannProof.QuartetoForcado
