import ClayRiemannProof.QuartetoForcado
import ClayRiemannProof.Fronteira.Ht
import ClayRiemannProof.Xi

/-!
# O resíduo como parâmetro: uma forma normal dos dois lados da reta, e a lei de de Bruijn

Perto de um par de zeros, a função real da reta (`Z(t)`, ou `Ξ(t) = ξ(½ + it)`) tem a forma local
`K·((t − t₀)² − κ)`. O mesmo parâmetro `κ` descreve as duas situações que os dados mostram
(README §36–§39, `computations/parametro/`):

* `κ > 0`: dois zeros na reta, a distância `2√κ` (para os quase-encontros de ζ, `κ = (Δγ/2)²`);
* `κ = 0`: zero duplo na reta;
* `κ < 0`: o par sai da reta e vira o quarteto `½ ± b ± iγ₀`, com `b = √(−κ)`; a reta vê só uma lombada sem
  troca de sinal, de altura `K·b²`, e perde dois zeros.

Aqui o modelo é o `QuartetoForcado.Q` (um par em `±iγ₀` com o parâmetro `κ`, coordenada `w = s − ½`).

1. **O resíduo na reta** (`Q_na_reta_real`, `residuo_na_reta`, `residuo_minimo`, `residuo_atingido`,
   `residuo_cota`, `b_do_residuo`). Com `κ = −b²`, o valor na reta é `(γ₀² − b² − t²)² + (2bγ₀)²`: nunca menor que
   o resíduo `m = (2bγ₀)²` (atingido em `t² = γ₀² − b²`), e sempre `≥ κ² = b⁴`. Do resíduo volta `b = √m/(2γ₀)`.
2. **As pontes do parâmetro** (`reta_ve_zero_iff`, `pontes_parametro`): são equivalentes `κ ≥ 0`, "todos os zeros
   do modelo na reta", "a reta vê um zero", "o resíduo na reta é 0" e "tempo de colisão `−2κ ≤ 0`".
3. **Tempo de colisão, uma fórmula para os dois lados** (`tempo_de_colisao`, `par_na_reta_kappa`,
   `quarteto_satura_de_bruijn`). No fluxo do calor de de Bruijn, `κ(t) = κ + t/2`; o modelo está todo na reta
   exatamente para `t ≥ −2κ`. Para um par na reta `−2κ = −Δγ²/2` (a cota de Lehmer, negativa); para um quarteto
   fora, `−2κ = 2b² = Δ²/2` com `Δ = 2b` (a altura em `z = 2γ`): exatamente a cota de de Bruijn, com igualdade, e
   a faixa encolhe como `(2b(t))² = Δ² − 2t`.
4. **A lei de de Bruijn com o resíduo** (`DeBruijnFaixa`, `lambda_le_de_faixa`, `faixa_de_xi`,
   `lambda_le_dois_b2`, `zeros_na_faixa`, `de_bruijn_meio`, `sem_residuo_lambda_le_zero`, `target_lambda_zero`,
   `residuo_de_lambda`, `sanduiche`). `DeBruijnFaixa` é o enunciado nomeado de de Bruijn (1950): se os zeros de
   `H₀` têm `|Im z| ≤ Δ`, os de `H_t` têm `(Im z)² ≤ max(Δ² − 2t, 0)`. Com ele e `H0_eh_xi`: se todo zero de `ξ` tem
   `|Re ρ − ½| ≤ b`, então `Λ ≤ 2b²`; como `ξ` não se anula em `Re ≥ 1` (Mathlib), `Λ ≤ ½` (o teorema de 1950);
   sem resíduo (`b = 0`, todo zero na reta), `Λ ≤ 0`, e com Rodgers–Tao `Λ = 0`; se `Λ > 0`, há zero com
   `|Re ρ − ½| > b` para todo `b` com `2b² < Λ`.
5. **Ler `b` da lombada** (`lombada_sem_troca`, `lombada_minimo`, `b_da_lombada`): com `K > 0`, `κ < 0`, a
   lombada `K((t − t₀)² − κ)` é positiva, tem mínimo `−Kκ` em `t₀` e segunda derivada `2K`, e
   `√(2·mínimo/segunda derivada) = √(−κ) = b`.
6. **A reta perde dois por par** (`S_reta_cai_dois`): se `N = N_reta + 2k`, então `S_reta = S − 2k`.
7. **"Absorver o ½" nas caudas é identidade, não lei** (`media_absorvida`, `media_s_sobre_dois`, `media_com_janela`;
   complementa `Absorcao`, README §38). Com `s_n = g_n/ḡ` e `ḡ` a média exata, a média de `½ + b(s_n − 1)` (ou de
   `s_n/2`) é `½` para todo `b` e **qualquer** família de gaps, com RH ou sem. O número `½ + b(s_n − 1)` é uma
   reetiquetagem do gap, não a parte real de zero nenhum. Com o comprimento da janela `L` no lugar de `Σ g`, a média é
   `(Σ g)/(2L)`.
8. **As frações exatas do par mais apertado** (`recorde_gap`, `recorde_media`, `recorde_s_bloco`,
   `recorde_lambda_exato`, `recorde_b_t6`, `recorde_fracao_na_bola`): o gap `6 184 036 434 821/10¹⁶` (`mdc = 1`), a
   média exata do bloco (menor que `1 680 000/7 190 341`), `s < 1/300`, o tempo de colisão `−g²/2` (o "fator 4" de
   `−d²/8` é a coordenada `z = 2γ`), e `b(−10⁻⁶)² = (λ − t)/2`, que não é `(3/5 000)²`.

9. **O ½ sem citar ½, e o que ele não diz** (`eixo_unico`, `zeros_espelhados`, `media_do_espelho`,
   `espelho_absorvida`, `espelho_conta`, `triviais_fora_de_xi`, `euler_meio_diverge`, `meio_nao_eh_inv_raiz`,
   `recorde_b_t5_t3`, `bola_relativa`). O ½ sai da equação funcional, não entra como hipótese: a única reta vertical
   que `s ↦ 1 − s̄` preserva é `Re s = ½`, e os zeros de `ξ` são levados uns nos outros por essa reflexão. Por isso a
   média de `Re` sobre um zero e o seu espelho é `½` **com ou sem RH**: média `½` não decide nada; o que decide é o
   resíduo `b` (`pontes_parametro`, `sanduiche`). O espelho do número absorvido `½ + b(s − 1)` é o de `2 − s`; um
   conjunto simétrico tem tantos `s < x` quanto `s > 2 − x` (`espelho_conta`), e o bloco tem 23 contra 247 382 (README
   §39). Os zeros triviais não são zeros de `ξ` (nenhum fluxo de `H_t` "chega" neles); `Σ p^{−1/2}` diverge (Mathlib),
   e `1/√p ≠ ½` para todo primo. O `b` do par recorde em `t = −10⁻⁵` e `−10⁻³` é `0,0022145…` e `0,0223585…`
   (não `11/5 000` e `14/625` exatos), e o erro da bola no gap é menor que `10⁻¹⁴` do gap (não 1,6 %).

`DeBruijnFaixa`, `H0_eh_xi` e `RodgersTao` são enunciados (`Prop`) de teoremas publicados, nunca `axiom`. Nada aqui
prova RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Parametro

open Complex ClayRiemannProof.QuartetoForcado

/-! ## 1. O resíduo na reta -/

/-- **Na reta (`w = it`) o modelo é real**: `Q(it) = ((t − γ₀)² − κ)((t + γ₀)² − κ)`. -/
theorem Q_na_reta_real (γ₀ κ t : ℝ) :
    Q γ₀ κ (I * t) = ((((t - γ₀) ^ 2 - κ) * ((t + γ₀) ^ 2 - κ) : ℝ) : ℂ) := by
  unfold Q
  have h1 : (I * (t : ℂ) - I * γ₀) ^ 2 + κ = -((t : ℂ) - γ₀) ^ 2 + κ := by
    linear_combination ((t : ℂ) - γ₀) ^ 2 * I_sq
  have h2 : (I * (t : ℂ) + I * γ₀) ^ 2 + κ = -((t : ℂ) + γ₀) ^ 2 + κ := by
    linear_combination ((t : ℂ) + γ₀) ^ 2 * I_sq
  rw [h1, h2]
  push_cast
  ring

/-- **O resíduo do quarteto na reta**: com `κ = −b²`, `Q(it) = (γ₀² − b² − t²)² + (2bγ₀)²`. -/
theorem residuo_na_reta (γ₀ b t : ℝ) :
    Q γ₀ (-(b ^ 2)) (I * t) = ((((γ₀ ^ 2 - b ^ 2 - t ^ 2) ^ 2 + (2 * b * γ₀) ^ 2) : ℝ) : ℂ) := by
  rw [Q_na_reta_real]
  congr 1
  ring

/-- **O resíduo é o mínimo**: na reta, o quarteto nunca deixa o valor descer abaixo de `(2bγ₀)²`. -/
theorem residuo_minimo (γ₀ b t : ℝ) :
    (2 * b * γ₀) ^ 2 ≤ (γ₀ ^ 2 - b ^ 2 - t ^ 2) ^ 2 + (2 * b * γ₀) ^ 2 :=
  le_add_of_nonneg_left (sq_nonneg _)

/-- **E é atingido** em `t = √(γ₀² − b²)` (para `b² ≤ γ₀²`, isto é, todo quarteto acima da altura `b`). -/
theorem residuo_atingido {γ₀ b : ℝ} (h : b ^ 2 ≤ γ₀ ^ 2) :
    (γ₀ ^ 2 - b ^ 2 - (Real.sqrt (γ₀ ^ 2 - b ^ 2)) ^ 2) ^ 2 + (2 * b * γ₀) ^ 2 = (2 * b * γ₀) ^ 2 := by
  rw [Real.sq_sqrt (by linarith)]
  ring

/-- **Cota uniforme**: com `κ < 0`, `κ² ≤ Q(it)` para todo `t` (cada fator é pelo menos `−κ`). -/
theorem residuo_cota {γ₀ κ : ℝ} (hκ : κ < 0) (t : ℝ) :
    κ ^ 2 ≤ ((t - γ₀) ^ 2 - κ) * ((t + γ₀) ^ 2 - κ) := by
  have h1 : -κ ≤ (t - γ₀) ^ 2 - κ := by linarith [sq_nonneg (t - γ₀)]
  have h2 : -κ ≤ (t + γ₀) ^ 2 - κ := by linarith [sq_nonneg (t + γ₀)]
  calc κ ^ 2 = (-κ) * (-κ) := by ring
    _ ≤ ((t - γ₀) ^ 2 - κ) * ((t + γ₀) ^ 2 - κ) := mul_le_mul h1 h2 (by linarith) (by linarith)

/-- **Do resíduo volta `b`**: `b = √m/(2γ₀)` com `m = (2bγ₀)²`. -/
theorem b_do_residuo {γ₀ b : ℝ} (hγ : 0 < γ₀) (hb : 0 ≤ b) :
    b = Real.sqrt ((2 * b * γ₀) ^ 2) / (2 * γ₀) := by
  rw [Real.sqrt_sq (by positivity), eq_div_iff (by positivity)]
  ring

/-! ## 2. As pontes do parâmetro -/

/-- **A reta vê um zero do modelo ⟺ `κ ≥ 0`.** -/
theorem reta_ve_zero_iff (γ₀ κ : ℝ) : (∃ t : ℝ, Q γ₀ κ (I * t) = 0) ↔ 0 ≤ κ := by
  constructor
  · rintro ⟨t, ht⟩
    by_contra hκ
    have hκ' : κ < 0 := lt_of_not_ge hκ
    rw [Q_na_reta_real, ofReal_eq_zero] at ht
    have h1 := residuo_cota (γ₀ := γ₀) hκ' t
    have h2 : 0 < κ ^ 2 := by nlinarith
    linarith
  · intro hκ
    refine ⟨γ₀ + Real.sqrt κ, ?_⟩
    rw [Q_na_reta_real, ofReal_eq_zero]
    have h : (γ₀ + Real.sqrt κ - γ₀) ^ 2 - κ = 0 := by
      rw [add_sub_cancel_left, Real.sq_sqrt hκ]
      ring
    rw [h, zero_mul]

/-- **As pontes do parâmetro `κ`**: são equivalentes (1) `κ ≥ 0`; (2) todos os zeros do modelo na reta;
(3) a reta vê um zero; (4) o resíduo na reta é `0` (`‖Q(it)‖` fica abaixo de todo `ε > 0`); (5) o tempo de colisão
`−2κ` é `≤ 0`. -/
theorem pontes_parametro (γ₀ κ : ℝ) :
    [0 ≤ κ,
      ∀ w : ℂ, Q γ₀ κ w = 0 → w.re = 0,
      ∃ t : ℝ, Q γ₀ κ (I * t) = 0,
      ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, ‖Q γ₀ κ (I * t)‖ < ε,
      -2 * κ ≤ 0].TFAE := by
  tfae_have 1 → 2 := fun h => Q_na_reta h
  tfae_have 2 → 1 := by
    intro h
    by_contra hκ
    obtain ⟨h1, -, -, -, hb⟩ := Q_quarteto (γ₀ := γ₀) (lt_of_not_ge hκ)
    have := h _ h1
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] at this
    linarith
  tfae_have 1 ↔ 3 := (reta_ve_zero_iff γ₀ κ).symm
  tfae_have 3 → 4 := by
    rintro ⟨t, ht⟩ ε hε
    exact ⟨t, by rw [ht, norm_zero]; exact hε⟩
  tfae_have 4 → 1 := by
    intro h
    by_contra hκ
    have hκ' : κ < 0 := lt_of_not_ge hκ
    obtain ⟨t, ht⟩ := h (κ ^ 2) (by nlinarith)
    rw [Q_na_reta_real, Complex.norm_real, Real.norm_eq_abs] at ht
    have h1 := residuo_cota (γ₀ := γ₀) hκ' t
    have h2 := le_abs_self (((t - γ₀) ^ 2 - κ) * ((t + γ₀) ^ 2 - κ))
    linarith
  tfae_have 1 ↔ 5 := by
    constructor <;> intro h <;> linarith
  tfae_finish

/-! ## 3. Tempo de colisão: uma fórmula para os dois lados -/

/-- **Tempo de colisão**: no fluxo do calor (`κ(t) = κ + t/2`), os zeros do modelo estão todos na reta exatamente
para `t ≥ −2κ`. -/
theorem tempo_de_colisao (γ₀ κ t : ℝ) :
    (∀ w : ℂ, Q γ₀ (κ + t / 2) w = 0 → w.re = 0) ↔ -2 * κ ≤ t := by
  have e : (∀ w : ℂ, Q γ₀ (κ + t / 2) w = 0 → w.re = 0) ↔ 0 ≤ κ + t / 2 :=
    (pontes_parametro γ₀ (κ + t / 2)).out 2 1
  rw [e]
  constructor <;> intro h <;> linarith

/-- **Um par na reta é o modelo com `κ = (Δγ/2)²`**: `γ₁` e `γ₂` são zeros, e o tempo de colisão `−2κ` é
`−(γ₂ − γ₁)²/2` (a cota de Lehmer do par). -/
theorem par_na_reta_kappa (γ₁ γ₂ : ℝ) :
    Q ((γ₁ + γ₂) / 2) (((γ₂ - γ₁) / 2) ^ 2) (I * γ₁) = 0 ∧
      Q ((γ₁ + γ₂) / 2) (((γ₂ - γ₁) / 2) ^ 2) (I * γ₂) = 0 ∧
      -2 * ((γ₂ - γ₁) / 2) ^ 2 = -((γ₂ - γ₁) ^ 2) / 2 := by
  refine ⟨?_, ?_, by ring⟩
  · rw [Q_na_reta_real, ofReal_eq_zero]
    ring
  · rw [Q_na_reta_real, ofReal_eq_zero]
    ring

/-- **O par mais apertado dos 14 380 683 zeros contíguos** (`Δγ = 6,184038·10⁻⁴`, README §36): `κ ≈ 9,56·10⁻⁸` e
tempo de colisão `−2κ ∈ (−1,9122·10⁻⁷; −1,9121·10⁻⁷)`, o `λ` já registrado. -/
theorem recorde_kappa :
    (956 / 10 ^ 10 : ℝ) < ((6184038 / 10 ^ 10) / 2) ^ 2 ∧ ((6184038 / 10 ^ 10 : ℝ) / 2) ^ 2 < 957 / 10 ^ 10 ∧
      -(19122 / 10 ^ 11 : ℝ) < -2 * ((6184038 / 10 ^ 10) / 2) ^ 2 ∧
      -2 * ((6184038 / 10 ^ 10 : ℝ) / 2) ^ 2 < -(19121 / 10 ^ 11) := by
  norm_num

/-- **O quarteto isolado satura a cota de de Bruijn**: a `b` da reta (`κ = −b²`), ele volta à reta exatamente em
`t = 2b² = Δ²/2` (`Δ = 2b`); antes disso o zero `√(b² − t/2) + iγ₀` está à distância `b(t) = √(b² − t/2)`, com
`(2b(t))² = Δ² − 2t`. -/
theorem quarteto_satura_de_bruijn (γ₀ b t : ℝ) :
    ((∀ w : ℂ, Q γ₀ (-(b ^ 2) + t / 2) w = 0 → w.re = 0) ↔ (2 * b) ^ 2 / 2 ≤ t) ∧
      (t ≤ 2 * b ^ 2 →
        Q γ₀ (-(b ^ 2) + t / 2) ((Real.sqrt (b ^ 2 - t / 2) : ℂ) + I * γ₀) = 0 ∧
          (2 * Real.sqrt (b ^ 2 - t / 2)) ^ 2 = (2 * b) ^ 2 - 2 * t) := by
  refine ⟨?_, fun ht => ⟨?_, ?_⟩⟩
  · rw [tempo_de_colisao]
    constructor <;> intro h <;> nlinarith
  · unfold Q
    have hs : ((Real.sqrt (b ^ 2 - t / 2) : ℝ) : ℂ) ^ 2 = ((b ^ 2 - t / 2 : ℝ) : ℂ) := by
      rw [← ofReal_pow, Real.sq_sqrt (by linarith)]
    have h0 : ((Real.sqrt (b ^ 2 - t / 2) : ℂ) + I * γ₀ - I * γ₀) ^ 2 + ((-(b ^ 2) + t / 2 : ℝ) : ℂ) = 0 := by
      rw [add_sub_cancel_right, hs]
      push_cast
      ring
    rw [h0, zero_mul]
  · rw [mul_pow, Real.sq_sqrt (by linarith)]
    ring

/-! ## 4. A lei de de Bruijn com o resíduo como parâmetro -/

open Fronteira

/-- **de Bruijn (1950), a faixa que encolhe** — enunciado nomeado: se todos os zeros de `H₀` têm `|Im z| ≤ Δ`,
então para `t ≥ 0` os zeros de `H_t` têm `(Im z)² ≤ max(Δ² − 2t, 0)`. -/
def DeBruijnFaixa : Prop :=
  ∀ Δ : ℝ, 0 ≤ Δ → (∀ z : ℂ, H 0 z = 0 → |z.im| ≤ Δ) →
    ∀ t : ℝ, 0 ≤ t → ∀ z : ℂ, H t z = 0 → z.im ^ 2 ≤ max (Δ ^ 2 - 2 * t) 0

/-- **`Λ ≤ Δ²/2`** a partir da faixa que encolhe. -/
theorem lambda_le_de_faixa (hdB : DeBruijnFaixa) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    (h : ∀ z : ℂ, H 0 z = 0 → |z.im| ≤ Δ) : deBruijnNewman ≤ Δ ^ 2 / 2 := by
  have hmem : Δ ^ 2 / 2 ∈ {t : ℝ | ∀ z : ℂ, H t z = 0 → z.im = 0} := by
    intro z hz
    have h1 := hdB Δ hΔ h (Δ ^ 2 / 2) (by positivity) z hz
    have h2 : max (Δ ^ 2 - 2 * (Δ ^ 2 / 2)) 0 = 0 := by
      rw [show Δ ^ 2 - 2 * (Δ ^ 2 / 2) = 0 by ring, max_self]
    rw [h2] at h1
    exact pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h1 (sq_nonneg _))
  unfold deBruijnNewman
  by_cases hb : BddBelow {t : ℝ | ∀ z : ℂ, H t z = 0 → z.im = 0}
  · exact csInf_le hb hmem
  · rw [Real.sInf_of_not_bddBelow hb]
    positivity

/-- **Do resíduo de `ξ` à faixa de `H₀`**: se todo zero de `ξ` tem `|Re ρ − ½| ≤ b`, todo zero de `H₀` tem
`|Im z| ≤ 2b` (`z` e `s = ½ + iz/2`). -/
theorem faixa_de_xi (hH0 : H0_eh_xi) {b : ℝ} (h : ∀ s : ℂ, Fronteira.xi s = 0 → |s.re - 1 / 2| ≤ b) :
    ∀ z : ℂ, H 0 z = 0 → |z.im| ≤ 2 * b := by
  intro z hz
  rw [hH0] at hz
  have hx : Fronteira.xi (1 / 2 + I * z / 2) = 0 := by
    rcases div_eq_zero_iff.mp hz with h' | h'
    · exact h'
    · norm_num at h'
  have h1 := h _ hx
  have hre : (1 / 2 + I * z / 2 : ℂ).re - 1 / 2 = -(z.im / 2) := by
    simp only [add_re, div_ofNat_re, one_re, mul_re, I_re, I_im, zero_mul, one_mul, zero_sub]
    ring
  rw [hre, abs_neg, abs_div, abs_two] at h1
  linarith

/-- **`Λ ≤ 2b²`**: o resíduo máximo `b` dos zeros de `ξ` controla `Λ`. -/
theorem lambda_le_dois_b2 (hH0 : H0_eh_xi) (hdB : DeBruijnFaixa) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ s : ℂ, Fronteira.xi s = 0 → |s.re - 1 / 2| ≤ b) : deBruijnNewman ≤ 2 * b ^ 2 := by
  have h1 := lambda_le_de_faixa hdB (by linarith : (0 : ℝ) ≤ 2 * b) (faixa_de_xi hH0 h)
  calc deBruijnNewman ≤ (2 * b) ^ 2 / 2 := h1
    _ = 2 * b ^ 2 := by ring

/-- As duas escritas de `ξ` (`Fronteira` e `Xi`) são a mesma função. -/
theorem xi_igual (s : ℂ) : Fronteira.xi s = Xi.xi s := by
  unfold Fronteira.xi Xi.xi
  ring

/-- **Os zeros de `ξ` estão na faixa aberta**: `|Re ρ − ½| < ½` (ζ não se anula em `Re ≥ 1`, Mathlib, e
`ξ(1 − s) = ξ(s)`). -/
theorem zeros_na_faixa {s : ℂ} (hs : Fronteira.xi s = 0) : |s.re - 1 / 2| < 1 / 2 := by
  rw [xi_igual] at hs
  have h1 : s.re < 1 := by
    by_contra h
    exact Xi.xi_ne_zero_of_one_le_re (not_lt.mp h) hs
  have h0 : 0 < s.re := by
    by_contra h
    have h' : 1 ≤ (1 - s).re := by
      rw [sub_re, one_re]
      linarith [not_lt.mp h]
    exact Xi.xi_ne_zero_of_one_le_re h' (by rw [Xi.xi_one_sub]; exact hs)
  rw [abs_lt]
  constructor <;> linarith

/-- **de Bruijn (1950): `Λ ≤ ½`**, no kernel a partir da faixa que encolhe e da faixa crítica (`b = ½`). -/
theorem de_bruijn_meio (hH0 : H0_eh_xi) (hdB : DeBruijnFaixa) : deBruijnNewman ≤ 1 / 2 := by
  have h1 := lambda_le_dois_b2 hH0 hdB (by norm_num : (0 : ℝ) ≤ 1 / 2) fun s hs => (zeros_na_faixa hs).le
  calc deBruijnNewman ≤ 2 * (1 / 2) ^ 2 := h1
    _ = 1 / 2 := by norm_num

/-- **Sem resíduo, `Λ ≤ 0`**: com todo zero de `ξ` na reta (`b = 0`), a faixa que encolhe dá `Λ ≤ 0`. -/
theorem sem_residuo_lambda_le_zero (hH0 : H0_eh_xi) (hdB : DeBruijnFaixa)
    (h : ∀ s : ℂ, Fronteira.xi s = 0 → s.re = 1 / 2) : deBruijnNewman ≤ 0 := by
  have h1 := lambda_le_dois_b2 hH0 hdB (b := 0) le_rfl fun s hs => by rw [h s hs]; simp
  simpa using h1

/-- **A meta implica `Λ = 0`**, com a faixa que encolhe, `H0_eh_xi` e Rodgers–Tao (sem usar `RH_iff_Lambda`). -/
theorem target_lambda_zero (hH0 : H0_eh_xi) (hdB : DeBruijnFaixa) (hRT : RodgersTao) (hT : Target) :
    deBruijnNewman = 0 :=
  le_antisymm
    (sem_residuo_lambda_le_zero hH0 hdB fun s hs =>
      (Xi.target_iff_xi.mp hT) s (by rw [← xi_igual]; exact hs))
    hRT

/-- **Se `Λ > 0`, algum zero está longe da reta**: para todo `b ≥ 0` com `2b² < Λ` há zero de `ξ` com
`|Re ρ − ½| > b` (o resíduo máximo é pelo menos `√(Λ/2)`). -/
theorem residuo_de_lambda (hH0 : H0_eh_xi) (hdB : DeBruijnFaixa) {b : ℝ} (hb : 0 ≤ b)
    (hΛ : 2 * b ^ 2 < deBruijnNewman) : ∃ s : ℂ, Fronteira.xi s = 0 ∧ b < |s.re - 1 / 2| := by
  by_contra hne
  have h' : ∀ s : ℂ, Fronteira.xi s = 0 → |s.re - 1 / 2| ≤ b := fun s hs =>
    le_of_not_gt fun hlt => hne ⟨s, hs, hlt⟩
  exact absurd (lambda_le_dois_b2 hH0 hdB hb h') (not_le.mpr hΛ)

/-- **O sanduíche**: `0 ≤ Λ ≤ 2b²` (Rodgers–Tao embaixo, o resíduo em cima). -/
theorem sanduiche (hH0 : H0_eh_xi) (hdB : DeBruijnFaixa) (hRT : RodgersTao) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ s : ℂ, Fronteira.xi s = 0 → |s.re - 1 / 2| ≤ b) :
    0 ≤ deBruijnNewman ∧ deBruijnNewman ≤ 2 * b ^ 2 :=
  ⟨hRT, lambda_le_dois_b2 hH0 hdB hb h⟩

/-! ## 5. Ler `b` da lombada -/

/-- **A lombada não troca de sinal**: com `K > 0` e `κ < 0`, `K((t − t₀)² − κ) > 0`. -/
theorem lombada_sem_troca {K κ : ℝ} (hK : 0 < K) (hκ : κ < 0) (t₀ t : ℝ) : 0 < K * ((t - t₀) ^ 2 - κ) :=
  mul_pos hK (by nlinarith [sq_nonneg (t - t₀)])

/-- **O mínimo da lombada é `−Kκ = Kb²`**, em `t₀`. -/
theorem lombada_minimo {K κ : ℝ} (hK : 0 < K) (t₀ t : ℝ) :
    K * ((t₀ - t₀) ^ 2 - κ) = K * (-κ) ∧ K * (-κ) ≤ K * ((t - t₀) ^ 2 - κ) := by
  refine ⟨by ring, mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg (t - t₀)]) hK.le⟩

/-- **`b` lido da lombada**: `√(2·mínimo/segunda derivada) = √(2·(−Kκ)/(2K)) = √(−κ)`. -/
theorem b_da_lombada {K κ : ℝ} (hK : 0 < K) : Real.sqrt (2 * (K * -κ) / (2 * K)) = Real.sqrt (-κ) := by
  congr 1
  field_simp

/-! ## 6. A reta perde dois por par -/

/-- **`S_reta = S − 2k`** quando `k` pares estão fora da reta (`N = N_reta + 2k`). -/
theorem S_reta_cai_dois (N Nreta k : ℕ) (θ : ℝ) (h : N = Nreta + 2 * k) :
    (Nreta : ℝ) - θ / Real.pi - 1 = ((N : ℝ) - θ / Real.pi - 1) - 2 * k := by
  rw [h]
  push_cast
  ring

/-! ## 7. "Absorver o ½" nas caudas: identidade, não lei -/

/-- **A média normalizada é 1 por construção**: com `ḡ = (Σ g)/m`, `Σ g_i/ḡ = m`, para qualquer família com soma
`≠ 0`. -/
private theorem soma_s {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ) (hg : ∑ i, g i ≠ 0) :
    ∑ i, g i / ((∑ j, g j) / m) = m := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [← Finset.sum_div]
  field_simp

/-- **A média de `½ + b(s − 1)` é `½` para todo `b` e todo bloco**: a mesma identidade, sem informação sobre os
zeros. -/
theorem media_absorvida {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ) (hg : ∑ i, g i ≠ 0) (b : ℝ) :
    (∑ i, (1 / 2 + b * (g i / ((∑ j, g j) / m) - 1))) / m = 1 / 2 := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, soma_s hm g hg]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- **A média de `s/2` é `½`** (a outra escrita da absorção). -/
theorem media_s_sobre_dois {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ) (hg : ∑ i, g i ≠ 0) :
    (∑ i, g i / ((∑ j, g j) / m) / 2) / m = 1 / 2 := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [← Finset.sum_div, soma_s hm g hg]
  field_simp

/-- **Com o comprimento da janela `L` no lugar da soma dos gaps**, a média de `s/2` é `(Σ g)/(2L)`: dá `½` só se
`Σ g = L`. -/
theorem media_com_janela {m : ℕ} (hm : 0 < m) (g : Fin m → ℝ) {L : ℝ} (hL : L ≠ 0) :
    (∑ i, g i / (L / m) / 2) / m = (∑ i, g i) / (2 * L) := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [← Finset.sum_div, ← Finset.sum_div]
  field_simp

/-! ## 8. As frações exatas do par mais apertado (centros das bolas da Arb, 17 casas) -/

/-- **O gap exato dos centros**: `6 184 036 434 821/10¹⁶`, irredutível. -/
theorem recorde_gap :
    (300017869072616295407189495341 : ℚ) / 10 ^ 17 - 300017869072616233566825147131 / 10 ^ 17 =
      6184036434821 / 10 ^ 16 ∧ Nat.gcd 6184036434821 (10 ^ 16) = 1 := by
  norm_num

/-- **A média exata do bloco** é `(γ_último − γ_primeiro)/14 380 682 =
335 999 974 185 419 717 845 531/(1,4380682·10²⁴)`, um pouco menor que `3 360 000/14 380 682 = 1 680 000/7 190 341`
(`mdc(3 360 000, 14 380 682) = 2`): o comprimento da janela não é a soma dos gaps. -/
theorem recorde_media :
    ((300017870247133681828170110023 : ℚ) / 10 ^ 17 - 75004383561789874102113066123 / (25 * 10 ^ 15)) /
        14380682 = 335999974185419717845531 / 1438068200000000000000000 ∧
      Nat.gcd 3360000 14380682 = 2 ∧ (3360000 : ℚ) / 14380682 = 1680000 / 7190341 ∧
      (335999974185419717845531 : ℚ) / 1438068200000000000000000 < 1680000 / 7190341 := by
  norm_num

/-- **`s` do par com a média do bloco**: `6 352 190 103 255 323 423/(2,4·10²¹) < 1/300`. -/
theorem recorde_s_bloco :
    ((6184036434821 : ℚ) / 10 ^ 16) / (1680000 / 7190341) = 6352190103255323423 / 2400000000000000000000 ∧
      (6352190103255323423 : ℚ) / 2400000000000000000000 < 1 / 300 := by
  norm_num

/-- **O tempo de colisão do par é `−g²/2`** (`−1,912…·10⁻⁷`), e `−(2g)²/8` é o mesmo número: o "fator 4" sobre
`−g²/8` vem da coordenada `z = 2γ`, não dos vizinhos. -/
theorem recorde_lambda_exato :
    -((6184036434821 : ℚ) / 10 ^ 16) ^ 2 / 2 = -38242306627193624181302041 / 200000000000000000000000000000000 ∧
      -(2 * ((6184036434821 : ℚ) / 10 ^ 16)) ^ 2 / 8 = -((6184036434821 : ℚ) / 10 ^ 16) ^ 2 / 2 := by
  norm_num

/-- **`b` em `t = −10⁻⁶` não é `3/5 000`**: `b² = (λ − t)/2 = 161 757 693 372 806 375 818 697 959/(4·10³²)`,
diferente de `(3/5 000)²`, e `0,000 635 9 < b < 0,000 636`. -/
theorem recorde_b_t6 :
    (-38242306627193624181302041 / 200000000000000000000000000000000 - (-(1 : ℚ) / 10 ^ 6)) / 2 =
        161757693372806375818697959 / 400000000000000000000000000000000 ∧
      (161757693372806375818697959 / 400000000000000000000000000000000 : ℚ) ≠ (3 / 5000) ^ 2 ∧
      (6359 / 10 ^ 7 : ℝ) < Real.sqrt (161757693372806375818697959 / 400000000000000000000000000000000) ∧
      Real.sqrt (161757693372806375818697959 / 400000000000000000000000000000000) < 636 / 10 ^ 6 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num

/-- **A fração mais simples na bola do gap**: `285 021/460 897 996` está em `[g − r, g + r]`, `r = 5,26·10⁻¹⁸` (a
soma dos dois raios). -/
theorem recorde_fracao_na_bola :
    (6184036434821 : ℚ) / 10 ^ 16 - 526 / 10 ^ 20 ≤ 285021 / 460897996 ∧
      (285021 : ℚ) / 460897996 ≤ 6184036434821 / 10 ^ 16 + 526 / 10 ^ 20 := by
  norm_num

/-! ## 9. O ½ sem citar ½, e o que ele não diz -/

open ComplexConjugate in
/-- **O ½ vem da reflexão, não de hipótese**: a única reta vertical `Re s = c` preservada por `s ↦ 1 − s̄` (a simetria
dos zeros que a equação funcional e a conjugação dão) é `c = ½`. -/
theorem eixo_unico (c : ℝ) : (∀ s : ℂ, s.re = c → (1 - conj s).re = c) ↔ c = 1 / 2 := by
  constructor
  · intro h
    have h1 := h (c : ℂ) (ofReal_re c)
    rw [sub_re, one_re, conj_re, ofReal_re] at h1
    linarith
  · intro hc s hs
    rw [sub_re, one_re, conj_re, hs, hc]
    norm_num

open ComplexConjugate in
/-- **Os zeros de `ξ` vêm espelhados**: `ξ(ρ) = 0 ⟹ ξ(1 − ρ̄) = 0` (`ξ(1 − s) = ξ(s)`, `ξ(s̄) = conj ξ(s)`). -/
theorem zeros_espelhados {s : ℂ} (hs : Xi.xi s = 0) : Xi.xi (1 - conj s) = 0 := by
  rw [Xi.xi_one_sub, Xi.xi_conj, hs, map_zero]

open ComplexConjugate in
/-- **Média `½` sempre**: para qualquer `ρ` (na reta ou fora), `(Re ρ + Re(1 − ρ̄))/2 = ½`. A média das partes reais
dos zeros é `½` com ou sem RH. -/
theorem media_do_espelho (ρ : ℂ) : (ρ.re + (1 - conj ρ).re) / 2 = 1 / 2 := by
  rw [sub_re, one_re, conj_re]
  ring

/-- **O espelho do número absorvido** `½ + b(s − 1)` é o número absorvido de `2 − s`. -/
theorem espelho_absorvida (b s : ℝ) : 1 - (1 / 2 + b * (s - 1)) = 1 / 2 + b * ((2 - s) - 1) := by
  ring

/-- **Um conjunto simétrico por `s ↦ 2 − s` tem tantos `s < x` quanto `s > 2 − x`.** -/
theorem espelho_conta (A : Finset ℝ) (hA : ∀ s ∈ A, 2 - s ∈ A) (x : ℝ) :
    (A.filter (fun s => s < x)).card = (A.filter (fun s => 2 - x < s)).card := by
  apply Finset.card_nbij' (fun s => 2 - s) (fun s => 2 - s)
  · intro s hs
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hs ⊢
    exact ⟨hA s hs.1, by linarith [hs.2]⟩
  · intro s hs
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hs ⊢
    exact ⟨hA s hs.1, by linarith [hs.2]⟩
  · intro s _
    simp only [sub_sub_cancel]
  · intro s _
    simp only [sub_sub_cancel]

/-- **Os zeros triviais não são zeros de `ξ`**: `ξ(−2(n + 1)) ≠ 0` (o fator `Γ` os cancela; nenhum zero de `H₀` está
lá, e nenhum fluxo de `H_t` "vira" zero trivial). -/
theorem triviais_fora_de_xi (n : ℕ) : Xi.xi ((-2 * ((n : ℝ) + 1) : ℝ) : ℂ) ≠ 0 := by
  intro h
  have h1 := zeros_na_faixa (s := ((-2 * ((n : ℝ) + 1) : ℝ) : ℂ)) (by rw [xi_igual]; exact h)
  rw [ofReal_re, abs_lt] at h1
  have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith [h1.1]

/-- **`Σ_p p^{−1/2}` diverge** (Mathlib: `Σ p^r` converge só para `r < −1`): em `Re s = ½` o produto de Euler não
converge absolutamente, e não pode ser citado ali. -/
theorem euler_meio_diverge : ¬ Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(1 / 2 : ℝ))) := by
  rw [Nat.Primes.summable_rpow]
  norm_num

/-- **`1/√p ≠ ½` para todo primo** (`1/√p = ½` só com `p = 4`). -/
theorem meio_nao_eh_inv_raiz (p : ℕ) (hp : p.Prime) : 1 / Real.sqrt p ≠ 1 / 2 := by
  intro h
  have h2 : Real.sqrt p = 2 := by
    have h' := congrArg (fun x => 1 / x) h
    simpa using h'
  have h4 : (p : ℝ) = 4 := by
    have h' := Real.sq_sqrt (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
    rw [h2] at h'
    linarith
  have h5 : p = 4 := by exact_mod_cast h4
  subst h5
  rcases hp.eq_one_or_self_of_dvd 2 (by norm_num) with h6 | h6 <;> omega

/-- **`b` do par recorde em `t = −10⁻⁵` e `t = −10⁻³`**: `b² = (λ − t)/2` com `λ = −g²/2`;
`0,0022145 < b(−10⁻⁵) < 0,0022146` e `0,0223585 < b(−10⁻³) < 0,0223586` (`11/5 000` e `14/625` são arredondamentos). -/
theorem recorde_b_t5_t3 :
    (-38242306627193624181302041 / 200000000000000000000000000000000 - (-(1 : ℚ) / 10 ^ 5)) / 2 =
        1961757693372806375818697959 / 400000000000000000000000000000000 ∧
      (-38242306627193624181302041 / 200000000000000000000000000000000 - (-(1 : ℚ) / 10 ^ 3)) / 2 =
        199961757693372806375818697959 / 400000000000000000000000000000000 ∧
      (22145 / 10 ^ 7 : ℝ) < Real.sqrt (1961757693372806375818697959 / 400000000000000000000000000000000) ∧
      Real.sqrt (1961757693372806375818697959 / 400000000000000000000000000000000) < 22146 / 10 ^ 7 ∧
      (223585 / 10 ^ 7 : ℝ) < Real.sqrt (199961757693372806375818697959 / 400000000000000000000000000000000) ∧
      Real.sqrt (199961757693372806375818697959 / 400000000000000000000000000000000) < 223586 / 10 ^ 7 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  · rw [Real.lt_sqrt (by norm_num)]
    norm_num
  · rw [Real.sqrt_lt' (by norm_num)]
    norm_num

/-- **O erro da bola no gap recorde é menor que `10⁻¹⁴` do gap**: `(5,26·10⁻¹⁸)/(6,18·10⁻⁴) < 10⁻¹⁴`. -/
theorem bola_relativa : (526 / 10 ^ 20 : ℚ) / (6184036434821 / 10 ^ 16) < 1 / 10 ^ 14 := by
  norm_num

end ClayRiemannProof.Parametro
