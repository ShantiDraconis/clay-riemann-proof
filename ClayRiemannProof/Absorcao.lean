import Mathlib

/-!
# A "absorção de ½" decidida no kernel

Um texto colado em 4/11/2026 propôs trocar a reta `Re s = ½` pela reparametrização `Re_abs = ½ + (s − 1)·b`, com `s`
o espaçamento normalizado entre zeros consecutivos e `b = 3/5 000` (ou `14/625`), e tirou daí cinco "teoremas": a reta
se dissolve numa nuvem (1), a média ½ se preserva (2), as caudas se compensam (3), um limite de dispersão (4) e a
invariância da média por toro, esfera em graus etc. (5). Este arquivo prova o que é verdade e refuta o que não é:

* `media_reAbs`, `media_normalizada_um`: a média ½ vale para **qualquer** lista de lacunas, porque a média de `s` é 1
  por construção (`s = lacuna / média das lacunas`). Os teoremas 2 e 3 não usam ζ; valem para Poisson e GUE também.
* `reAbs_eq_meio_iff`, `media_meio_sem_ponto_meio`: o teorema 1 é só "`Re_abs = ½` exatamente quando `s = 1`".
  Média ½ não põe nenhum ponto em ½. É a definição que se escolheu, não uma propriedade dos zeros.
* `fracoes_do_texto`, `cauda_longa_b_pequeno`: as frações conferidas. 2 497/5 000 é o limite `s → 0` (em `s = 1/100` dá
  249 703/500 000), 2 503/5 000 é `s = 2`, e 653/1 250 sai de `b = 14/625` com `s = 2`, não de `b = 3/5 000` com `s > 3`
  (aí `Re_abs` fica entre 1 253/2 500 e 653/1 250 para `3 < s < 4`; o maior `s` medido é 3,686).
* `theta_media_contraexemplo`, `media_theta_negativa`: o teorema 5 é falso. `θ = 360°·(s − 1)/(s + 1)` é côncava em
  `s > 0`, então com média de `s` igual a 1 a média de θ é **negativa** sempre que algum `s ≠ 1` (Jensen estrito).
  Nos 23 111 812 espaçamentos das 45 faixas a média é −16,17°, não 180° nem 0°.
* `soma_primos_sse`, `soma_quadrados_primos_sse`: onde o ½ entra em Euler. `Σ_p p^{−σ}` converge só para `σ > 1` (é a
  convergência absoluta do produto de Euler; em `σ = ½` o produto diverge), e `Σ_p (p^{−σ})² = Σ_p p^{−2σ}` converge
  exatamente para `σ > ½`. O ½ é a fronteira da soma dos quadrados (a variância de `log ζ` no modelo de Bohr–Jessen e
  de Selberg), não a do produto, e não força `σ = ½`.
* `tcol_coordenadas`, `tcol_do_texto_fora_do_intervalo`: em `H_t` os zeros de `H_0` estão em `x = 2γ`; um par a
  distância `Δγ` colide em `t ≈ −(2Δγ)²/8 = −Δγ²/2`. O texto usou `d = Δγ` na fórmula de `x` e achou um quarto disso;
  o seu `t_col` do par 12 363 175 635 090/091 cai fora do intervalo certificado (`par_mais_fragil_continuacao4`).
* `gbar_nao_exato`: a lacuna média da janela de 45 faixas é `5 400 000/23 111 813` (fração irredutível). 1 350 000/5
  777 953 é uma aproximação (23 111 813 não é múltiplo de 4); o mesmo vale para 1 680 000/7 190 341 na janela antiga,
  cuja fração exata é `1 120 000/4 793 561`.

O que o bloco certificado prova continua sendo RH até `3 000 181 222 471`, condicional às janelas da Arb como hipóteses
nomeadas (`Continuacao.rhAteZ_continuacao4`). Nada aqui prova ou refuta RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Absorcao

open Finset

/-- A reparametrização proposta: `Re_abs = ½ + (s − 1)·b`. É uma função do espaçamento `s` escolhida à mão, não uma
propriedade de ζ. -/
noncomputable def reAbs (b s : ℝ) : ℝ := 1 / 2 + (s - 1) * b

/-- **Teoremas 2 e 3 do texto**: se a média dos `s` é 1, a média de `Re_abs` é ½ e as caudas se compensam
(`Σ (sᵢ − 1)·b = 0`), qualquer que seja `b` e qualquer que seja a lista. -/
theorem media_reAbs {n : ℕ} (b : ℝ) (s : Fin n → ℝ) (hs : ∑ i, s i = n) :
    ∑ i, reAbs b (s i) = n / 2 := by
  have h1 : ∑ i, (s i - 1) * b = 0 := by
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, hs]
    simp
  simp only [reAbs, Finset.sum_add_distrib, h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  ring

/-- **A média de `s` é 1 por construção**: com a lacuna média `ḡ = (Σ gᵢ)/n`, `Σ gᵢ/ḡ = n` para qualquer lista de
lacunas (de ζ, do GUE ou de Poisson). -/
theorem media_normalizada_um {n : ℕ} (g : Fin n → ℝ) (hg : ∑ i, g i ≠ 0) :
    ∑ i, g i / ((∑ j, g j) / n) = n := by
  rw [← Finset.sum_div]
  field_simp

/-- **Teorema 1 do texto, o que ele diz de fato**: com `b ≠ 0`, `Re_abs = ½` exatamente quando `s = 1`. -/
theorem reAbs_eq_meio_iff {b s : ℝ} (hb : b ≠ 0) : reAbs b s = 1 / 2 ↔ s = 1 := by
  unfold reAbs
  constructor
  · intro h
    have h0 : (s - 1) * b = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h1 | h1
    · linarith
    · exact absurd h1 hb
  · rintro rfl
    ring

/-- **Média ½ não põe nenhum ponto em ½**: `s = ½` e `s = 3/2` (média 1) dão `Re_abs` médio ½ e nenhum dos dois é ½. -/
theorem media_meio_sem_ponto_meio :
    reAbs (3 / 5000) (1 / 2) ≠ 1 / 2 ∧ reAbs (3 / 5000) (3 / 2) ≠ 1 / 2 ∧
      (reAbs (3 / 5000) (1 / 2) + reAbs (3 / 5000) (3 / 2)) / 2 = 1 / 2 := by
  unfold reAbs
  norm_num

/-- **As frações do texto, conferidas.** -/
theorem fracoes_do_texto :
    reAbs (3 / 5000) (71 / 10000) = 24970213 / 50000000 ∧
    reAbs (3 / 5000) 0 = 2497 / 5000 ∧
    reAbs (3 / 5000) (1 / 100) = 249703 / 500000 ∧
    reAbs (3 / 5000) 2 = 2503 / 5000 ∧
    reAbs (3 / 5000) 3 = 1253 / 2500 ∧
    reAbs (14 / 625) 2 = 653 / 1250 := by
  unfold reAbs
  norm_num

/-- Com `b = 3/5 000`, a cauda longa observada (`3 < s < 4`) fica entre 1 253/2 500 = 0,5012 e 653/1 250 = 0,5224,
sem chegar a 653/1 250. -/
theorem cauda_longa_b_pequeno {s : ℝ} (hs : 3 < s) (hs4 : s < 4) :
    1253 / 2500 < reAbs (3 / 5000) s ∧ reAbs (3 / 5000) s < 653 / 1250 := by
  unfold reAbs
  constructor <;> linarith

/-- O ângulo do texto: `θ(s) = 360°·(s − 1)/(s + 1)`. -/
noncomputable def theta (s : ℝ) : ℝ := 360 * (s - 1) / (s + 1)

/-- **O teorema 5 é falso**: `s = ½` e `s = 3/2` têm média 1, e a média de θ é −24°, não 180° (nem 0°). -/
theorem theta_media_contraexemplo : (theta (1 / 2) + theta (3 / 2)) / 2 = -24 := by
  unfold theta
  norm_num

/-- A reta tangente em `s = 1` fica por cima de θ (θ é côncava em `s > 0`), e só toca em `s = 1`. -/
theorem theta_le_tangente {s : ℝ} (hs : 0 < s) : theta s ≤ 180 * (s - 1) := by
  unfold theta
  rw [div_le_iff₀ (by linarith)]
  nlinarith [sq_nonneg (s - 1)]

theorem theta_lt_tangente {s : ℝ} (hs : 0 < s) (h1 : s ≠ 1) : theta s < 180 * (s - 1) := by
  unfold theta
  rw [div_lt_iff₀ (by linarith)]
  have : 0 < (s - 1) ^ 2 := by
    have : s - 1 ≠ 0 := sub_ne_zero.mpr h1
    positivity
  nlinarith

/-- **Jensen estrito**: espaçamentos positivos com média 1, não todos iguais a 1, têm média de θ negativa. -/
theorem media_theta_negativa {n : ℕ} (s : Fin n → ℝ) (hpos : ∀ i, 0 < s i) (hs : ∑ i, s i = n)
    (h : ∃ i, s i ≠ 1) : ∑ i, theta (s i) < 0 := by
  obtain ⟨j, hj⟩ := h
  have hlt : ∑ i, theta (s i) < ∑ i, 180 * (s i - 1) :=
    Finset.sum_lt_sum (fun i _ => theta_le_tangente (hpos i)) ⟨j, Finset.mem_univ _, theta_lt_tangente (hpos j) hj⟩
  have h0 : ∑ i, 180 * (s i - 1) = 0 := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hs]
    simp
  linarith

/-- **Euler**: `Σ_p p^{−σ}` converge exatamente para `σ > 1` (a convergência absoluta do produto de Euler). -/
theorem soma_primos_sse (σ : ℝ) : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-σ)) ↔ 1 < σ := by
  rw [Nat.Primes.summable_rpow]
  constructor <;> intro h <;> linarith

/-- **Onde está o ½**: `Σ_p (p^{−σ})² = Σ_p p^{−2σ}` converge exatamente para `σ > ½`. -/
theorem soma_quadrados_primos_sse (σ : ℝ) :
    Summable (fun p : Nat.Primes => ((p : ℝ) ^ (-σ)) ^ 2) ↔ 1 / 2 < σ := by
  have hf : (fun p : Nat.Primes => ((p : ℝ) ^ (-σ)) ^ 2) = fun p : Nat.Primes => (p : ℝ) ^ (-(2 * σ)) := by
    funext p
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    push_cast
    ring
  rw [hf, Nat.Primes.summable_rpow]
  constructor <;> intro h <;> linarith

/-- **O tempo de colisão em coordenadas de γ**: com `x = 2γ`, `(2Δγ)²/8 = Δγ²/2`, quatro vezes `Δγ²/8`. -/
theorem tcol_coordenadas (Δγ : ℝ) : (2 * Δγ) ^ 2 / 8 = 4 * (Δγ ^ 2 / 8) ∧ (2 * Δγ) ^ 2 / 8 = Δγ ^ 2 / 2 := by
  constructor <;> ring

/-- O `t_col` do texto para o par 12 363 175 635 090/091 (−91 872 225/267 077 926 961 672 ≈ −3,44·10⁻⁷) fica fora do
intervalo certificado `[−1,74·10⁻⁶, −1,39·10⁻⁶]` de `Continuacao.par_mais_fragil_continuacao4`. -/
theorem tcol_do_texto_fora_do_intervalo : -(139 : ℝ) / 100000000 < -91872225 / 267077926961672 := by
  norm_num

/-- **A lacuna média exata das 45 faixas** é `5 400 000/23 111 813`; as frações do texto são aproximações. -/
theorem gbar_nao_exato :
    (1350000 : ℚ) / 5777953 ≠ 5400000 / 23111813 ∧ (1680000 : ℚ) / 7190341 ≠ 3360000 / 14380683 ∧
      (3360000 : ℚ) / 14380683 = 1120000 / 4793561 ∧ Nat.gcd 5400000 23111813 = 1 ∧ Nat.gcd 1120000 4793561 = 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

end ClayRiemannProof.Absorcao
