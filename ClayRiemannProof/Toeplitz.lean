import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# O núcleo finito do teorema de Connes–van Suijlekom (§64)

Connes e van Suijlekom (arXiv 2511.23257) provam que, se o mínimo do espectro de uma forma de Toeplitz contínua é um
autovalor simples com autofunção par, a transformada de Fourier dessa autofunção só tem zeros reais. O passo (1) da
prova é finito:

> **Uma matriz de Toeplitz hermitiana, semidefinida positiva, `n × n`, cujo núcleo é a reta gerada por um vetor `ξ ≠ 0`
> (posto `n − 1`), tem `P(z) = Σ ξ_j z^j` com todos os zeros no círculo unitário.**

Aqui esse passo está provado no kernel (`zeros_no_circulo`), por um argumento elementar:

1. Se `P(a) = 0`, a divisão sintética dá `ξ = S q − a q`, com `q` os coeficientes de `P/(z − a)` (`divisao`) e `S` o
   deslocamento (multiplicar por `z`).
2. A forma de Toeplitz não muda sob o deslocamento (`forma_desloca`): `⟨T Sq, Sq⟩ = ⟨T q, q⟩`.
3. Como `Tξ = 0`, `⟨Tξ, q⟩ = ⟨Tξ, Sq⟩ = 0` dá `A = |a|²·A` com `A = ⟨T q, q⟩`. Se `|a| ≠ 1`, `A = 0`.
4. Semidefinida positiva com `⟨T q, q⟩ = 0` dá `T q = 0`, e o mesmo para `S q`. Pelo núcleo de dimensão 1, `q` e
   `S q` são múltiplos de `ξ`. Daí `S q = κ·q` com `q` de grau `≤ n − 2`, o que força `q = 0` (`desloca_autovetor`), e
   então `ξ = 0`. Contradição.

`exemplo_2x2` mostra que as hipóteses não são vazias: `[[1, −1], [−1, 1]]` satisfaz todas.

O passo contínuo (Toeplitz → forma de Weil, com Hurwitz) e a hipótese (S) de simplicidade e paridade não estão aqui.
Nada aqui prova RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Toeplitz

open Finset Matrix

open scoped ComplexOrder

/-! ## 1. Vetores em `ℕ`, deslocamento e a forma de Toeplitz -/

/-- O vetor de `Fin n` estendido por zero a `ℕ`. -/
def ext {n : ℕ} (v : Fin n → ℂ) (j : ℕ) : ℂ := if h : j < n then v ⟨j, h⟩ else 0

/-- A restrição de um vetor de `ℕ` a `Fin n`. -/
def toFin {n : ℕ} (u : ℕ → ℂ) : Fin n → ℂ := fun i => u i

/-- O deslocamento (multiplicar o polinômio por `z`): `(Sh u) 0 = 0`, `(Sh u) (j + 1) = u j`. -/
def Sh (u : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | j + 1 => u j

/-- A forma de Toeplitz com símbolo `t`: `Σ_{i,j < n} ū_i t(i − j) w_j`. -/
def forma (n : ℕ) (t : ℤ → ℂ) (u w : ℕ → ℂ) : ℂ :=
  ∑ i ∈ range n, ∑ j ∈ range n, star (u i) * t ((i : ℤ) - j) * w j

theorem ext_val {n : ℕ} (v : Fin n → ℂ) (i : Fin n) : ext v i = v i := by
  simp [ext, i.isLt]

theorem ext_toFin {n : ℕ} {u : ℕ → ℂ} (hu : ∀ j, n ≤ j → u j = 0) : ext (toFin (n := n) u) = u := by
  funext j
  unfold ext toFin
  by_cases h : j < n
  · simp [h]
  · simp [h, hu j (not_lt.mp h)]

/-- **A forma da matriz é a forma de Toeplitz em `ℕ`.** -/
theorem forma_eq {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ} {t : ℤ → ℂ}
    (hToe : ∀ i j : Fin n, T i j = t ((i : ℤ) - j)) (x y : Fin n → ℂ) :
    star x ⬝ᵥ T *ᵥ y = forma n t (ext x) (ext y) := by
  simp only [dotProduct, mulVec, Pi.star_apply, forma]
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range n, star (ext x i) * t ((i : ℤ) - j) * ext y j) n]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun j => star (ext x i) * t ((i : ℤ) - j) * ext y j) n, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hToe, ext_val, ext_val]
  ring

/-- A forma é linear no segundo argumento. -/
theorem forma_sub_mul (n : ℕ) (t : ℤ → ℂ) (u v w : ℕ → ℂ) (a : ℂ) :
    forma n t u (fun j => v j - a * w j) = forma n t u v - a * forma n t u w := by
  unfold forma
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **A forma é hermitiana** quando o símbolo é: `t(j − i) = conj t(i − j)`. -/
theorem forma_herm {n : ℕ} {t : ℤ → ℂ}
    (hH : ∀ i j : ℕ, i < n → j < n → t ((j : ℤ) - i) = star (t ((i : ℤ) - j))) (u w : ℕ → ℂ) :
    forma n t u w = star (forma n t w u) := by
  unfold forma
  rw [Finset.sum_comm, star_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [star_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hH i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)]
  simp only [star_mul', star_star]
  ring

/-- **A forma de Toeplitz não muda sob o deslocamento**, para vetores de grau `≤ m − 1` em dimensão `m + 1`. -/
theorem forma_desloca {m : ℕ} (t : ℤ → ℂ) {u w : ℕ → ℂ} (hu : ∀ j, m ≤ j → u j = 0)
    (hw : ∀ j, m ≤ j → w j = 0) : forma (m + 1) t (Sh u) (Sh w) = forma (m + 1) t u w := by
  have L : forma (m + 1) t (Sh u) (Sh w) =
      ∑ i ∈ range m, ∑ j ∈ range m, star (u i) * t ((i : ℤ) - j) * w j := by
    unfold forma
    rw [Finset.sum_range_succ']
    simp only [Sh, star_zero, zero_mul, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_range_succ']
    simp only [mul_zero, add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show ((i + 1 : ℕ) : ℤ) - ((j + 1 : ℕ) : ℤ) = (i : ℤ) - j by push_cast; ring]
  have R : forma (m + 1) t u w = ∑ i ∈ range m, ∑ j ∈ range m, star (u i) * t ((i : ℤ) - j) * w j := by
    unfold forma
    rw [Finset.sum_range_succ]
    simp only [hu m le_rfl, star_zero, zero_mul, Finset.sum_const_zero, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_range_succ, hw m le_rfl, mul_zero, add_zero]
  rw [L, R]

/-! ## 2. A divisão sintética -/

/-- Os coeficientes de `P(z)/(z − a)`: `q_j = Σ_{j < k < n} ξ_k a^{k − j − 1}`. -/
def quoc (n : ℕ) (X : ℕ → ℂ) (a : ℂ) (j : ℕ) : ℂ :=
  ∑ k ∈ Ico (j + 1) n, X k * a ^ (k - j - 1)

theorem quoc_zero {n : ℕ} {X : ℕ → ℂ} {a : ℂ} {j : ℕ} (hj : n ≤ j + 1) : quoc n X a j = 0 := by
  simp [quoc, Finset.Ico_eq_empty_of_le hj]

/-- **A divisão sintética**: se `P(a) = Σ_{k<n} X_k a^k = 0` e `X` se anula a partir de `n`, então
`X = S q − a q` com `q = quoc n X a`. -/
theorem divisao {n : ℕ} {X : ℕ → ℂ} {a : ℂ} (hX : ∀ j, n ≤ j → X j = 0)
    (hP : ∑ k ∈ range n, X k * a ^ k = 0) (j : ℕ) :
    X j = Sh (quoc n X a) j - a * quoc n X a j := by
  cases j with
  | zero =>
    simp only [Sh, zero_sub]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [hX 0 le_rfl, quoc_zero (by omega), mul_zero, neg_zero]
    · rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn] at hP
      have h : a * quoc n X a 0 = ∑ k ∈ Ico (0 + 1) n, X k * a ^ k := by
        unfold quoc
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk1 : k ≠ 0 := by
          have := (Finset.mem_Ico.mp hk).1
          omega
        rw [show k - 0 - 1 = k - 1 by omega, mul_left_comm, mul_pow_sub_one hk1]
      rw [h]
      simp only [pow_zero, mul_one] at hP
      linear_combination hP
  | succ i =>
    simp only [Sh]
    by_cases hi : i + 1 < n
    · unfold quoc
      rw [Finset.sum_eq_sum_Ico_succ_bot hi, Finset.mul_sum]
      have h : ∀ k ∈ Ico (i + 1 + 1) n, a * (X k * a ^ (k - (i + 1) - 1)) = X k * a ^ (k - i - 1) := by
        intro k hk
        have hk2 := (Finset.mem_Ico.mp hk).1
        rw [show k - i - 1 = (k - (i + 1) - 1) + 1 by omega, pow_succ]
        ring
      rw [Finset.sum_congr rfl h, show i + 1 - i - 1 = 0 by omega, pow_zero, mul_one]
      ring
    · rw [hX (i + 1) (by omega), quoc_zero (by omega), quoc_zero (by omega), mul_zero, sub_zero]

/-! ## 3. O deslocamento não tem autovetor de grau baixo -/

/-- **Se `S q = κ·q` em `0..m` e `q` se anula a partir de `m`, então `q = 0`.** -/
theorem desloca_autovetor {m : ℕ} {Q : ℕ → ℂ} (hQ : ∀ j, m ≤ j → Q j = 0) (κ : ℂ)
    (h : ∀ j, j < m + 1 → Sh Q j = κ * Q j) : ∀ j, Q j = 0 := by
  by_cases hκ : κ = 0
  · intro j
    by_cases hj : j < m
    · have := h (j + 1) (by omega)
      simp only [Sh, hκ, zero_mul] at this
      exact this
    · exact hQ j (not_lt.mp hj)
  · intro j
    induction j with
    | zero =>
      have := h 0 (by omega)
      simp only [Sh] at this
      rcases mul_eq_zero.mp this.symm with h1 | h1
      · exact absurd h1 hκ
      · exact h1
    | succ k ih =>
      by_cases hk : k + 1 < m + 1
      · have := h (k + 1) hk
        simp only [Sh, ih] at this
        rcases mul_eq_zero.mp this.symm with h1 | h1
        · exact absurd h1 hκ
        · exact h1
      · exact hQ (k + 1) (by omega)

/-! ## 4. O teorema -/

/-- **O núcleo finito de Connes–van Suijlekom.** Seja `T` uma matriz de Toeplitz (`T i j = t(i − j)`) hermitiana e
semidefinida positiva, `n × n`, cujo núcleo é a reta gerada por `ξ ≠ 0`. Então todo zero de `P(z) = Σ ξ_j z^j` está no
círculo unitário. -/
theorem zeros_no_circulo {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ} {t : ℤ → ℂ}
    (hToe : ∀ i j : Fin n, T i j = t ((i : ℤ) - j)) (hT : T.PosSemidef)
    {ξ : Fin n → ℂ} (hξ : T *ᵥ ξ = 0) (hξ0 : ξ ≠ 0)
    (hker : ∀ v : Fin n → ℂ, T *ᵥ v = 0 → ∃ c : ℂ, v = c • ξ)
    {a : ℂ} (ha : ∑ i : Fin n, ξ i * a ^ (i : ℕ) = 0) : ‖a‖ = 1 := by
  cases n with
  | zero => exact absurd (funext fun i => i.elim0) hξ0
  | succ m =>
  -- notação
  set X : ℕ → ℂ := ext ξ with hXdef
  have hX : ∀ j, m + 1 ≤ j → X j = 0 := fun j hj => by
    have hj' : ¬ j < m + 1 := by omega
    simp [hXdef, ext, hj']
  have hP : ∑ k ∈ range (m + 1), X k * a ^ k = 0 := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => X k * a ^ k) (m + 1)]
    simpa only [hXdef, ext_val] using ha
  set Q : ℕ → ℂ := quoc (m + 1) X a with hQdef
  have hQ : ∀ j, m ≤ j → Q j = 0 := fun j hj => quoc_zero (by omega)
  have hSQ : ∀ j, m + 1 ≤ j → Sh Q j = 0 := by
    intro j hj
    cases j with
    | zero => omega
    | succ i => exact hQ i (by omega)
  have hdiv : X = fun j => Sh Q j - a * Q j := funext (divisao hX hP)
  -- os vetores em `Fin (m + 1)`
  have eQ : ext (toFin (n := m + 1) Q) = Q := ext_toFin fun j hj => hQ j (by omega)
  have eSQ : ext (toFin (n := m + 1) (Sh Q)) = Sh Q := ext_toFin hSQ
  -- a simetria hermitiana do símbolo
  have hH : ∀ i j : ℕ, i < m + 1 → j < m + 1 → t ((j : ℤ) - i) = star (t ((i : ℤ) - j)) := by
    intro i j hi hj
    have := hT.isHermitian.apply ⟨j, hj⟩ ⟨i, hi⟩
    rw [hToe, hToe] at this
    exact this.symm
  -- as duas equações
  have E1 : forma (m + 1) t Q (Sh Q) - a * forma (m + 1) t Q Q = 0 := by
    have h0 := forma_eq hToe (toFin (n := m + 1) Q) ξ
    rw [hξ, dotProduct_zero, eQ, ← hXdef, hdiv, forma_sub_mul] at h0
    exact h0.symm
  have E2 : forma (m + 1) t (Sh Q) (Sh Q) - a * forma (m + 1) t (Sh Q) Q = 0 := by
    have h0 := forma_eq hToe (toFin (n := m + 1) (Sh Q)) ξ
    rw [hξ, dotProduct_zero, eSQ, ← hXdef, hdiv, forma_sub_mul] at h0
    exact h0.symm
  set A := forma (m + 1) t Q Q with hAdef
  have hAstar : A = star A := forma_herm hH Q Q
  have hSS : forma (m + 1) t (Sh Q) (Sh Q) = A := forma_desloca t hQ hQ
  have hSQQ : forma (m + 1) t (Sh Q) Q = star (forma (m + 1) t Q (Sh Q)) := forma_herm hH (Sh Q) Q
  have hC : forma (m + 1) t Q (Sh Q) = a * A := by linear_combination E1
  rw [hSS, hSQQ, hC, star_mul', ← hAstar] at E2
  have hfat : A * (1 - a * star a) = 0 := by linear_combination E2
  rcases mul_eq_zero.mp hfat with hA0 | h1
  · -- `A = 0` leva a `ξ = 0`
    exfalso
    have k1 : T *ᵥ toFin (n := m + 1) Q = 0 := by
      apply hT.dotProduct_mulVec_zero_iff.mp
      rw [forma_eq hToe, eQ]
      exact hA0
    have k2 : T *ᵥ toFin (n := m + 1) (Sh Q) = 0 := by
      apply hT.dotProduct_mulVec_zero_iff.mp
      rw [forma_eq hToe, eSQ, hSS]
      exact hA0
    obtain ⟨c, hc⟩ := hker _ k1
    obtain ⟨d, hd⟩ := hker _ k2
    have hQX : ∀ j, j < m + 1 → Q j = c * X j := by
      intro j hj
      have := congrFun hc ⟨j, hj⟩
      simp only [toFin, Pi.smul_apply, smul_eq_mul] at this
      rw [this, hXdef]
      simp [ext, hj]
    have hSX : ∀ j, j < m + 1 → Sh Q j = d * X j := by
      intro j hj
      have := congrFun hd ⟨j, hj⟩
      simp only [toFin, Pi.smul_apply, smul_eq_mul] at this
      rw [this, hXdef]
      simp [ext, hj]
    have hQ0 : ∀ j, Q j = 0 := by
      by_cases hc0 : c = 0
      · intro j
        by_cases hj : j < m + 1
        · rw [hQX j hj, hc0, zero_mul]
        · exact hQ j (by omega)
      · refine desloca_autovetor hQ (d / c) fun j hj => ?_
        rw [hSX j hj, hQX j hj]
        field_simp
    apply hξ0
    funext i
    have := congrFun hdiv i
    simp only [hQ0, mul_zero, sub_zero] at this
    have hS0 : Sh Q i = 0 := by
      cases h : (i : ℕ) with
      | zero => simp [Sh]
      | succ k => simp [Sh, hQ0 k]
    rw [hS0] at this
    rw [← ext_val ξ i, ← hXdef, this]
    rfl
  · -- `a · ā = 1`
    have h2 : a * star a = 1 := by linear_combination -h1
    have h3 : ((‖a‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← h2]
      push_cast
      exact (Complex.mul_conj' a).symm
    have h4 : ‖a‖ ^ 2 = 1 := by exact_mod_cast h3
    have h5 := norm_nonneg a
    nlinarith [sq_nonneg (‖a‖ - 1), sq_nonneg (‖a‖ + 1)]

/-! ## 5. As hipóteses não são vazias -/

/-- O símbolo `t(0) = 1`, `t(±1) = −1`. -/
def simbolo2 (k : ℤ) : ℂ := if k = 0 then 1 else -1

/-- `T = [[1, −1], [−1, 1]]`. -/
def T2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, -1; -1, 1]

/-- `ξ = (1, 1)`. -/
def ξ2 : Fin 2 → ℂ := ![1, 1]

theorem T2_toeplitz : ∀ i j : Fin 2, T2 i j = simbolo2 ((i : ℤ) - j) := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [T2, simbolo2]

/-- A linha `(1, −1)`. -/
def R2 : Matrix (Fin 1) (Fin 2) ℂ := !![1, -1]

theorem T2_psd : T2.PosSemidef := by
  have h : T2 = R2ᴴ * R2 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [T2, R2, Matrix.mul_apply]
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem T2_xi : T2 *ᵥ ξ2 = 0 := by
  ext i
  fin_cases i <;> simp [T2, ξ2, mulVec, dotProduct, Fin.sum_univ_two]

theorem T2_nucleo : ∀ v : Fin 2 → ℂ, T2 *ᵥ v = 0 → ∃ c : ℂ, v = c • ξ2 := by
  intro v hv
  have h0 := congrFun hv 0
  simp [T2, mulVec, dotProduct, Fin.sum_univ_two] at h0
  refine ⟨v 0, ?_⟩
  ext i
  fin_cases i
  · simp [ξ2]
  · simp [ξ2]
    linear_combination -h0

theorem xi2_ne_zero : ξ2 ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [ξ2] at this

/-- **Exemplo**: `T = [[1, −1], [−1, 1]]` satisfaz todas as hipóteses de `zeros_no_circulo`, e o zero `−1` de
`P(z) = 1 + z` está no círculo, como o teorema garante. -/
theorem exemplo_2x2 : ‖(-1 : ℂ)‖ = 1 :=
  zeros_no_circulo T2_toeplitz T2_psd T2_xi xi2_ne_zero T2_nucleo (by simp [ξ2, Fin.sum_univ_two])

end ClayRiemannProof.Toeplitz
