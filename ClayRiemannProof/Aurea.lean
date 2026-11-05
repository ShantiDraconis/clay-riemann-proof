import ClayRiemannProof.HeightThirteen
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# φ, Fibonacci, `1/√p` e os quartetos: o que é exato

O que liga de fato a razão áurea, Fibonacci e `π` à zeta (README §50), no kernel:

* **`1/√5` é o mesmo número três vezes**: `F_n/φⁿ → 1/√5` (Binet, `fib_sobre_phi_pow`); `‖5^{−s}‖ = 1/√5` na reta
  (`norma_cinco_na_reta`); e `F_n²·|φ − F_{n+1}/F_n| → 1/√5` (`hurwitz_phi`), a constante de Hurwitz da melhor
  aproximação racional, atingida por `φ`.
* **Fibonacci obedece ao fator de Euler de `L(s, χ₅)`**: `p ∣ F_{p − (5/p)}` para os 46 primos menores que 200
  (`entrada_ate_200`). É a lei de `ℚ(√5)`, cuja zeta é `ζ(s)·L(s, χ₅)` e cuja unidade é `φ`.
* **`π` em Fibonacci**: o termo principal da zeta de Fibonacci `Σ F_n^{−s}` tem polos onde `φ^{−s} = 1`, isto é,
  `s = 2πim/log φ` (`polos_fibonacci`), espaçados `2π/log φ ≈ 13,057`.
* **Os quadrados de Fibonacci ladrilham um retângulo**: `Σ_{k ≤ n} F_k² = F_n·F_{n+1}` (`fibonacci_ladrilha`).
* **O quarteto é um retângulo, nunca um quadrado**: as quatro simetrias `s, 1 − s, s̄, 1 − s̄` são involuções que
  comutam (`quarteto_klein`: grupo de Klein, sem rotação de 90° nem de 120°); os lados são `|2 Re ρ − 1| < 1` e
  `2|Im ρ| > 26` (`quarteto_retangulo`, com a faixa sem zeros até 13).
* **O ângulo do quarteto tende a meia volta de π**: a diagonal faz com o eixo real um ângulo a menos de `1/26` rad de
  `π/2` (`angulo_do_quarteto`): `√−1 = e^{iπ/2}` é o "½" que aparece.
* **No círculo de Li**, `ρ` e `1 − ρ̄` vão em pontos inversos: `|1 − 1/ρ|·|1 − 1/(1 − ρ̄)| = 1` (`li_inversao`).
* **O toro das fases**: `log 2/log 3` não é racional (`fases_independentes`), então as fases `(t log 2, t log 3)`
  nunca fecham uma órbita.

**O que isto não é**: nenhuma dessas identidades diz onde estão os zeros de `ζ`; `φ` entra em `L(s, χ₅)` e em
Fibonacci, não na posição dos zeros de `ζ`. Nos zeros fora da reta que existem (Epstein, Davenport–Heilbronn) o
teste numérico não acha `φ` (`computations/aurea/`). `OPEN_MATH = true`.
-/

open Real Complex Filter Topology
open scoped goldenRatio

namespace ClayRiemannProof.Aurea

open ClayRiemannProof.Zeta.Symmetry

/-! ## 1. `1/√5` três vezes -/

/-- **Binet**: `F_n/φⁿ → 1/√5`. -/
theorem fib_sobre_phi_pow : Tendsto (fun n : ℕ => (Nat.fib n : ℝ) / φ ^ n) atTop (𝓝 (1 / √5)) := by
  have hφ : φ ≠ 0 := goldenRatio_ne_zero
  have e : ∀ n : ℕ, (Nat.fib n : ℝ) / φ ^ n = (1 - (ψ / φ) ^ n) / √5 := by
    intro n
    rw [coe_fib_eq, div_right_comm, sub_div, div_self (pow_ne_zero n hφ), ← div_pow]
  simp_rw [e]
  have hq : |ψ / φ| < 1 := by
    rw [abs_div, abs_of_pos goldenRatio_pos, div_lt_one goldenRatio_pos, abs_lt]
    constructor <;> nlinarith [neg_one_lt_goldenConj, goldenConj_neg, one_lt_goldenRatio]
  have h := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq
  have h2 := (h.const_sub 1).div_const (√5)
  simpa using h2

/-- **`‖5^{−s}‖ = 1/√5` na reta** `Re s = ½`. -/
theorem norma_cinco_na_reta {s : ℂ} (hs : s.re = 1 / 2) : ‖((5 : ℝ) : ℂ) ^ (-s)‖ = 1 / √5 := by
  rw [norm_cpow_eq_rpow_re_of_pos (by norm_num), neg_re, hs, rpow_neg (by norm_num), sqrt_eq_rpow]
  exact (one_div _).symm

/-- **O limite de Binet é o módulo do termo de Euler de 5 na reta.** -/
theorem binet_eh_euler_5 {s : ℂ} (hs : s.re = 1 / 2) :
    Tendsto (fun n : ℕ => (Nat.fib n : ℝ) / φ ^ n) atTop (𝓝 ‖((5 : ℝ) : ℂ) ^ (-s)‖) := by
  rw [norma_cinco_na_reta hs]
  exact fib_sobre_phi_pow

/-- `F_n·(F_{n+1} − φF_n) = ((−1)ⁿ − ψ^{2n})/√5` (de `F_{n+1} − φF_n = ψⁿ` e Binet). -/
theorem fib_vezes_erro (n : ℕ) :
    (Nat.fib n : ℝ) * ((Nat.fib (n + 1) : ℝ) - φ * Nat.fib n) = ((-1) ^ n - ψ ^ (2 * n)) / √5 := by
  rw [fib_succ_sub_goldenRatio_mul_fib, coe_fib_eq]
  have : φ ^ n * ψ ^ n = (-1) ^ n := by rw [← mul_pow, goldenRatio_mul_goldenConj]
  rw [pow_mul, sq, mul_pow] at *
  field_simp
  rw [← this]
  ring

/-- **Hurwitz**: `F_n·|F_{n+1} − φF_n| = F_n²·|φ − F_{n+1}/F_n| → 1/√5`. -/
theorem hurwitz_phi :
    Tendsto (fun n : ℕ => (Nat.fib n : ℝ) * |(Nat.fib (n + 1) : ℝ) - φ * Nat.fib n|) atTop (𝓝 (1 / √5)) := by
  have hψ2 : |ψ ^ 2| < 1 := by
    rw [abs_pow, sq_lt_one_iff₀ (abs_nonneg _), abs_lt]
    exact ⟨neg_one_lt_goldenConj, goldenConj_neg.trans zero_lt_one⟩
  have h0 := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hψ2
  have e : ∀ n : ℕ, (Nat.fib n : ℝ) * |(Nat.fib (n + 1) : ℝ) - φ * Nat.fib n| =
      |1 - (-1) ^ n * (ψ ^ 2) ^ n| / √5 := by
    intro n
    have ea : (Nat.fib n : ℝ) * |(Nat.fib (n + 1) : ℝ) - φ * Nat.fib n| =
        |(Nat.fib n : ℝ) * ((Nat.fib (n + 1) : ℝ) - φ * Nat.fib n)| := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (Nat.fib n))]
    rw [ea, fib_vezes_erro, abs_div, abs_of_pos (by positivity : (0 : ℝ) < √5), ← pow_mul]
    congr 1
    have h1 : |((-1 : ℝ)) ^ n| = 1 := by simp
    rw [show (1 : ℝ) - (-1) ^ n * ψ ^ (2 * n) = (-1) ^ n * ((-1) ^ n - ψ ^ (2 * n)) by
      rw [mul_sub, ← pow_add, ← two_mul, pow_mul]; norm_num]
    rw [abs_mul, h1, one_mul]
  simp_rw [e]
  have h3 : Tendsto (fun n : ℕ => (-1 : ℝ) ^ n * (ψ ^ 2) ^ n) atTop (𝓝 0) := by
    have hb : ∀ n : ℕ, ‖(-1 : ℝ) ^ n * (ψ ^ 2) ^ n‖ ≤ ‖(ψ ^ 2) ^ n‖ := by
      intro n; rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact squeeze_zero_norm hb (by simpa using h0.norm)
  have h4 := ((h3.const_sub 1).abs).div_const (√5)
  simpa using h4

/-! ## 2. Fibonacci e o fator de Euler de `L(s, χ₅)` -/

/-- Onde o primo `p` entra em Fibonacci: `p − (5/p)`, isto é, `p − 1` se `p ≡ ±1 (mod 5)`, `p + 1` se `p ≡ ±2`, e
`5` para `p = 5`. -/
def entrada (p : ℕ) : ℕ := if p % 5 = 0 then p else if p % 5 = 1 ∨ p % 5 = 4 then p - 1 else p + 1

/-- Os 46 primos menores que 200. -/
def primos200 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83,
  89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199]

theorem primos200_primos : ∀ p ∈ primos200, p.Prime := by
  intro p hp
  simp only [primos200, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- **A lei de entrada**: `p ∣ F_{p − (5/p)}` para os 46 primos menores que 200 (kernel). -/
theorem entrada_ate_200 : ∀ p ∈ primos200, p ∣ Nat.fib (entrada p) := by
  have h : primos200.all (fun p => Nat.fib (entrada p) % p == 0) = true := by decide +kernel
  intro p hp
  have := List.all_eq_true.mp h p hp
  simpa [Nat.dvd_iff_mod_eq_zero] using this

/-! ## 3. `π` em Fibonacci: os polos da zeta de Fibonacci -/

/-- **`φ^{−s} = 1` em `s = 2πim/log φ`**: ali o termo `φ^{−s}/(1 − φ^{−s})` da zeta de Fibonacci tem polo; os
polos ficam em `Re s = 0`, espaçados `2π/log φ`. -/
theorem polos_fibonacci (m : ℤ) : ((φ : ℝ) : ℂ) ^ (-(2 * π * m * I / (Real.log φ : ℂ))) = 1 := by
  have hl : (Real.log φ : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos one_lt_goldenRatio).ne'
  have hφ : ((φ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast goldenRatio_ne_zero
  rw [cpow_def_of_ne_zero hφ, ← ofReal_log goldenRatio_pos.le]
  have : (Real.log φ : ℂ) * -(2 * π * m * I / (Real.log φ : ℂ)) = ((-m : ℤ) : ℂ) * (2 * π * I) := by
    field_simp
    push_cast
    ring
  rw [this, exp_int_mul_two_pi_mul_I]

/-! ## 4. Os quadrados de Fibonacci ladrilham um retângulo -/

/-- **`Σ_{k ≤ n} F_k² = F_n·F_{n+1}`**: os quadrados de lados `F_1, …, F_n` cobrem o retângulo `F_n × F_{n+1}`. -/
theorem fibonacci_ladrilha (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.fib k ^ 2 = Nat.fib n * Nat.fib (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.fib_add_two]
    ring

/-! ## 5. O quarteto: retângulo de Klein, nunca quadrado, ângulo perto de meia volta -/

/-- **O grupo das quatro simetrias é o de Klein**: todas involuções, e `1 − s` comuta com `s̄`. Não há rotação de
90° (quadrado) nem de 120° (triângulo). -/
theorem quarteto_klein (s : ℂ) : tensao (tensao s) = s ∧ espelho (espelho s) = s ∧ torcao (torcao s) = s ∧
    tensao (espelho s) = espelho (tensao s) :=
  ⟨tensao_tensao s, espelho_espelho s, torcao_torcao s, (torcao_eq s).1.symm.trans (torcao_eq s).2⟩

theorem norma_menos_torcao (ρ : ℂ) : ‖ρ - torcao ρ‖ = |2 * ρ.re - 1| := by
  have : ρ - torcao ρ = ((2 * ρ.re - 1 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [torcao]
    ring
  rw [this, Complex.norm_real, Real.norm_eq_abs]

theorem norma_menos_espelho (ρ : ℂ) : ‖ρ - espelho ρ‖ = 2 * |ρ.im| := by
  have : ρ - espelho ρ = ((2 * ρ.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [espelho]
    ring
  rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- **O quarteto é um retângulo de lados `< 1` e `> 26`**: nunca quadrado. -/
theorem quarteto_retangulo {ρ : ℂ} (hρ : ρ ∈ Z) : ‖ρ - torcao ρ‖ < 1 ∧ 26 < ‖ρ - espelho ρ‖ := by
  rw [norma_menos_torcao, norma_menos_espelho]
  have h13 := HeightThirteen.primeiro_zero_entre.2 ρ hρ
  obtain ⟨-, h0, h1⟩ := hρ
  constructor
  · rw [abs_lt]; constructor <;> linarith
  · linarith

/-- **O ângulo da diagonal do quarteto fica a menos de `1/26` rad de `π/2`**: com `b = Re ρ − ½ ≠ 0`,
`0 < π/2 − arctan(|Im ρ|/|b|) < 1/26`. -/
theorem angulo_do_quarteto {ρ : ℂ} (hρ : ρ ∈ Z) (hb : ρ.re ≠ 1 / 2) :
    0 < π / 2 - Real.arctan (|ρ.im| / |ρ.re - 1 / 2|) ∧ π / 2 - Real.arctan (|ρ.im| / |ρ.re - 1 / 2|) < 1 / 26 := by
  have h13 := HeightThirteen.primeiro_zero_entre.2 ρ hρ
  obtain ⟨-, h0, h1⟩ := hρ
  have hb0 : 0 < |ρ.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hb)
  have hb1 : |ρ.re - 1 / 2| < 1 / 2 := by rw [abs_lt]; constructor <;> linarith
  have hg : 0 < |ρ.im| := by linarith
  have hx : 0 < |ρ.im| / |ρ.re - 1 / 2| := div_pos hg hb0
  rw [← arctan_inv_of_pos hx, inv_div]
  have hy : 0 < |ρ.re - 1 / 2| / |ρ.im| := div_pos hb0 hg
  refine ⟨arctan_pos.mpr hy, (arctan_lt_self hy).trans ?_⟩
  rw [div_lt_iff₀ hg]
  nlinarith

/-! ## 6. O círculo de Li e o toro das fases -/

/-- **No círculo de Li, `ρ` e `1 − ρ̄` são pontos inversos**: `|1 − 1/ρ|·|1 − 1/(1 − ρ̄)| = 1`. -/
theorem li_inversao {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    ‖1 - 1 / ρ‖ * ‖1 - 1 / (1 - (starRingEnd ℂ) ρ)‖ = 1 := by
  have h1' : 1 - (starRingEnd ℂ) ρ ≠ 0 := by
    intro e
    apply h1
    have : (starRingEnd ℂ) ρ = 1 := by linear_combination -e
    simpa using congrArg (starRingEnd ℂ) this
  have e1 : 1 - 1 / ρ = (ρ - 1) / ρ := by field_simp
  have e2 : 1 - 1 / (1 - (starRingEnd ℂ) ρ) = -(starRingEnd ℂ) ρ / (1 - (starRingEnd ℂ) ρ) := by
    field_simp
    ring
  have n1 : ‖1 - (starRingEnd ℂ) ρ‖ = ‖ρ - 1‖ := by
    rw [← Complex.norm_conj, map_sub, map_one, Complex.conj_conj, norm_sub_rev]
  have hρn : ‖ρ‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have hn1 : ‖ρ - 1‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h1)
  rw [e1, e2, norm_div, norm_div, norm_neg, Complex.norm_conj, n1]
  field_simp

/-- **As fases de 2 e 3 são independentes**: `log 2/log 3` não é racional. -/
theorem fases_independentes (m n : ℕ) (hn : 0 < n) : Real.log 2 / Real.log 3 ≠ (m : ℝ) / n := by
  intro h
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : Real.log ((2 : ℝ) ^ n) = Real.log ((3 : ℝ) ^ m) := by
    rw [Real.log_pow, Real.log_pow]
    field_simp at h
    linarith
  have e2 : ((2 ^ n : ℕ) : ℝ) = ((3 ^ m : ℕ) : ℝ) := by
    push_cast
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity)) e
  have e3 : 2 ^ n = 3 ^ m := by exact_mod_cast e2
  have a : 2 ^ n % 2 = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    simp [pow_succ]
  have b : 3 ^ m % 2 = 1 := by
    rw [Nat.pow_mod]; norm_num
  omega

/-! ## 7. Quatro cópias da estrutura girada de 90° em torno de ½ -/

/-- A rotação de 90° em torno de `½`: `s ↦ ½ + i(s − ½)`. -/
noncomputable def rot90 (s : ℂ) : ℂ := 1 / 2 + I * (s - 1 / 2)

theorem rot90_re (s : ℂ) : (rot90 s).re = 1 / 2 - s.im := by
  simp [rot90]
  ring

theorem rot90_im (s : ℂ) : (rot90 s).im = s.re - 1 / 2 := by
  simp [rot90]

/-- **Duas rotações de 90° são a tensão `s ↦ 1 − s`** (a de 180° é uma simetria de `ζ`), e quatro voltam ao início:
as quatro cópias formam o grupo cíclico de ordem 4, e com `s ↦ s̄` o grupo do quadrado (diedral de ordem 8). -/
theorem rot90_dois (s : ℂ) : rot90 (rot90 s) = tensao s := by
  simp only [rot90, tensao]
  linear_combination (s - 1 / 2) * I_sq

theorem rot90_rot90 (s : ℂ) : rot90 (rot90 s) = tensao s ∧ rot90 (rot90 (rot90 (rot90 s))) = s :=
  ⟨rot90_dois s, by rw [rot90_dois (rot90 (rot90 s)), rot90_dois s, tensao_tensao]⟩

/-- **A cópia girada de 90° (ou de 270°) tira todo zero não trivial da faixa crítica**: `Re(rot90 ρ) = ½ − Im ρ`,
e `|Im ρ| > 13`. -/
theorem rot90_tira_da_faixa {ρ : ℂ} (hρ : ρ ∈ Z) : rot90 ρ ∉ Z ∧ rot90 (rot90 (rot90 ρ)) ∉ Z := by
  have h13 := HeightThirteen.primeiro_zero_entre.2 ρ hρ
  have e3 : rot90 (rot90 (rot90 ρ)) = rot90 (tensao ρ) := by rw [(rot90_rot90 ρ).1]
  have h13' := HeightThirteen.primeiro_zero_entre.2 _ (tensao_mem_Z hρ)
  constructor
  · rintro ⟨-, h0, h1⟩
    rw [rot90_re] at h0 h1
    rcases lt_abs.mp h13 with h | h <;> linarith
  · rw [e3]
    rintro ⟨-, h0, h1⟩
    rw [rot90_re] at h0 h1
    rcases lt_abs.mp h13' with h | h <;> linarith

/-- **Os zeros de `ζ` não têm a simetria do quadrado**: nenhum conjunto não vazio de zeros não triviais é fechado pela
rotação de 90°, e `Z` não é vazio. As quatro cópias giradas não são todas `ζ`: só as de 0° e 180° são. -/
theorem zeros_sem_simetria_do_quadrado : ¬ ∀ ρ ∈ Z, rot90 ρ ∈ Z := by
  intro h
  obtain ⟨ρ, hρ⟩ := ClayRiemannProof.CertifiedZeros.FirstZero.Z_nao_vazio
  exact (rot90_tira_da_faixa hρ).1 (h ρ hρ)

/-- **Na cruz das quatro cópias, um zero fora da reta fica colado aos braços**: a órbita de `ρ` pelo grupo do quadrado
são os 8 pontos `½ ± b ± iγ` e `½ ± γ ± ib`; cada um faz com o braço mais próximo da cruz (a reta crítica ou a sua
cópia girada, o eixo real) um ângulo `arctan(|b|/|γ|) < 1/26`. -/
theorem octeto_colado_aos_bracos {ρ : ℂ} (hρ : ρ ∈ Z) (hb : ρ.re ≠ 1 / 2) :
    0 < Real.arctan (|ρ.re - 1 / 2| / |ρ.im|) ∧ Real.arctan (|ρ.re - 1 / 2| / |ρ.im|) < 1 / 26 := by
  have h := angulo_do_quarteto hρ hb
  have h13 := HeightThirteen.primeiro_zero_entre.2 ρ hρ
  have hb0 : 0 < |ρ.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hb)
  have hx : 0 < |ρ.im| / |ρ.re - 1 / 2| := div_pos (by linarith) hb0
  rw [← arctan_inv_of_pos hx, inv_div] at h
  exact h

end ClayRiemannProof.Aurea
