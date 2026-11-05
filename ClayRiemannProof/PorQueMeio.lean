import ClayRiemannProof.Proporcao
import ClayRiemannProof.Maquina
import ClayRiemannProof.Geometrias
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Por que ½: o que se prova e o que não se prova

Este arquivo põe no kernel cada ingrediente da explicação "por que os zeros têm parte real ½" e marca, também no
kernel, onde ela deixa de ser prova.

**O que se prova.**

1. `meio_fechado`: `σ ↦ 1 − σ` leva `[0, 1]` nele mesmo, troca 0 com 1, e o único ponto fixo é ½.
2. `euler_meia_volta`: `e^{iπ} = −1` (Euler, `π`, `√−1`), e a meia volta em torno de ½ é `s ↦ 1 − s`, a simetria
   de `ζ`.
3. `se_ha_uma_reta_ela_eh_meio`: **se** todos os zeros estiverem numa mesma reta vertical, ela é `Re s = ½`. Não
   poderia ser outro valor.
4. `bordas_fechadas`: nenhum zero não trivial tem `Re ≤ 0` ou `Re ≥ 1` (início fechado em 0, fim fechado em 1); fechar
   o fim em `a` é fechar o início em `1 − a`; e a RH é fechar todos os fins acima de ½.
5. `rh_iff_um_sobre_raiz_p`: a RH equivale a "todo zero dá a todo primo o peso exato `1/√p`", e basta o primo 2.
   `peso_mede`: o peso é `p^{−Re s}`; ele **mede** a parte real, não a fixa.
6. `um_sobre_raiz_tende_a_zero` e `cauda_diverge_na_reta`: `1/√p → 0`, mas `Σ_p 1/√p = ∞`. Na reta, o produto de
   Euler não converge, e a cauda dos primos não trava nada diretamente.

**O que não se prova.** `ingredientes_nao_travam`: o modelo da §54 tem a estrutura inteira (faixa, a meia volta de
Euler em ½, o espelho, altura acima de 13) e um ponto em que **nenhum** primo tem o peso `1/√p`. Os ingredientes não
tornam impossível um zero fora da reta.

**A lógica** (`quatro_valores`): a RH é verdadeira ou falsa, nunca as duas. Se for falsa, a refutação é uma conta
finita (`Maquina.refutacao_finita`, com a equivalência de Lagarias como hipótese nomeada). Por isso "indeterminado"
(nem demonstrável nem refutável) só seria possível com a RH verdadeira.

Nada aqui prova RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.PorQueMeio

open Filter Topology Complex ClayRiemannProof.Zeta.Symmetry ClayRiemannProof.Estrutura

/-! ## 1. O meio fechado, Euler e a única reta possível -/

/-- **O meio fechado**: `σ ↦ 1 − σ` leva `[0, 1]` em `[0, 1]`, troca 0 com 1, e só fixa ½. -/
theorem meio_fechado : (∀ σ ∈ Set.Icc (0 : ℝ) 1, 1 - σ ∈ Set.Icc (0 : ℝ) 1) ∧ (1 - (0 : ℝ) = 1 ∧ 1 - (1 : ℝ) = 0) ∧
    ∀ σ : ℝ, 1 - σ = σ ↔ σ = 1 / 2 :=
  ⟨fun σ ⟨h0, h1⟩ => ⟨by linarith, by linarith⟩, ⟨by norm_num, by norm_num⟩,
    fun σ => ⟨fun h => by linarith, fun h => by rw [h]; norm_num⟩⟩

/-- **Euler, `π` e `√−1`**: `e^{iπ} = −1`, e a meia volta em torno de ½ é `s ↦ 1 − s`. -/
theorem euler_meia_volta : Complex.exp (Real.pi * I) = -1 ∧ ∀ s, gira (1 / 2) Real.pi s = tensao s :=
  ⟨Complex.exp_pi_mul_I, gira_meio_meia_volta⟩

/-- **Se há uma reta, ela é ½**: se todo zero não trivial tem parte real `c`, então `c = ½`. -/
theorem se_ha_uma_reta_ela_eh_meio {c : ℝ} (h : ∀ ρ ∈ Z, ρ.re = c) : c = 1 / 2 := by
  obtain ⟨ρ, hρ⟩ := ClayRiemannProof.CertifiedZeros.FirstZero.Z_nao_vazio
  have h1 := h ρ hρ
  have h2 := h _ (tensao_mem_Z hρ)
  rw [re_tensao] at h2
  linarith

/-- **As bordas fechadas**: nenhum zero não trivial nas bordas; fechar o fim em `a` é fechar o início em `1 − a`; e a
RH é fechar todos os fins acima de ½. Ninguém sabe fechar um fim `a < 1` (nem a quase-RH). -/
theorem bordas_fechadas : FimLivre 1 ∧ InicioLivre 0 ∧ (∀ a : ℝ, 0 < a → (FimLivre a ↔ InicioLivre (1 - a))) ∧
    (RiemannHypothesis ↔ ∀ a : ℝ, 1 / 2 < a → FimLivre a) :=
  ⟨fimLivre_um, inicioLivre_zero, fun _ ha => fim_iff_inicio ha, riemann_iff_fim⟩

/-! ## 2. `1/√p`: o peso de cada primo -/

/-- **O peso de cada primo é `p^{−Re s}`**: depende só da parte real. -/
theorem peso_mede {q : ℝ} (hq : 0 < q) (s : ℂ) : ‖(q : ℂ) ^ (-s)‖ = q ^ (-s.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hq, Complex.neg_re]

/-- **`‖q^{−s}‖ = 1/√q ⟺ Re s = ½`.** -/
theorem norma_primo_iff {q : ℝ} (hq : 1 < q) (s : ℂ) : ‖(q : ℂ) ^ (-s)‖ = 1 / Real.sqrt q ↔ s.re = 1 / 2 := by
  rw [← Geometrias.circulo_eh_reta hq s, Complex.normSq_eq_norm_sq]
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr (by linarith)
  have e : (1 / Real.sqrt q) ^ 2 = 1 / q := by rw [div_pow, one_pow, Real.sq_sqrt (by linarith)]
  constructor
  · intro h
    rw [h, e]
  · intro h
    rw [← e] at h
    exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

theorem rh_iff_reta : RiemannHypothesis ↔ ∀ ρ ∈ Z, ρ.re = 1 / 2 := by
  rw [riemann_iff_torcao]
  exact forall₂_congr fun ρ _ => torcao_fixo_iff ρ

/-- **A RH em termos de `1/√p`**: todo zero dá a todo primo o peso exato `1/√p`; e basta testar o primo 2. -/
theorem rh_iff_um_sobre_raiz_p : List.TFAE
    [ RiemannHypothesis,
      ∀ ρ ∈ Z, ∀ p : ℕ, p.Prime → ‖((p : ℝ) : ℂ) ^ (-ρ)‖ = 1 / Real.sqrt p,
      ∀ ρ ∈ Z, ‖((2 : ℝ) : ℂ) ^ (-ρ)‖ = 1 / Real.sqrt 2 ] := by
  tfae_have 1 → 2 := fun h ρ hρ p hp =>
    (norma_primo_iff (by exact_mod_cast hp.one_lt) ρ).mpr (rh_iff_reta.mp h ρ hρ)
  tfae_have 2 → 3 := fun h ρ hρ => by
    have := h ρ hρ 2 Nat.prime_two
    simpa using this
  tfae_have 3 → 1 := fun h => rh_iff_reta.mpr fun ρ hρ => (norma_primo_iff (by norm_num) ρ).mp (h ρ hρ)
  tfae_finish

/-! ## 3. A cauda dos primos -/

/-- **`1/√p → 0`.** -/
theorem um_sobre_raiz_tende_a_zero : Tendsto (fun p : ℕ => 1 / Real.sqrt p) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).comp tendsto_natCast_atTop_atTop
  refine h.congr fun p => ?_
  simp only [Function.comp_apply, Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg p), one_div]

/-- **Na reta, a cauda dos primos não converge**: `Σ_p 1/√p = ∞`, porque já `Σ_p 1/p = ∞` (Euler). O produto de
Euler só converge absolutamente em `Re s > 1`; em `Re s = ½` os primos não travam nada termo a termo. -/
theorem cauda_diverge_na_reta : ¬ Summable (fun p : Nat.Primes => 1 / Real.sqrt ((p : ℕ) : ℝ)) := by
  intro h
  apply Nat.Primes.not_summable_one_div
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) h
  have hp : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.one_lt.le
  apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by linarith))
  calc Real.sqrt ((p : ℕ) : ℝ) ≤ Real.sqrt (((p : ℕ) : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = ((p : ℕ) : ℝ) := Real.sqrt_sq (by linarith)

/-! ## 4. Os ingredientes não travam -/

/-- **Os mesmos ingredientes, um zero fora**: o modelo da §54 tem a estrutura inteira (faixa, a meia volta de Euler em
½, o espelho, altura acima de 13) e um ponto em que nenhum primo tem o peso `1/√p`. -/
theorem ingredientes_nao_travam : ∃ W : Set ℂ, EstruturaDeRiemann W ∧
    ∃ ρ ∈ W, ∀ p : ℕ, p.Prime → ‖((p : ℝ) : ℂ) ^ (-ρ)‖ ≠ 1 / Real.sqrt p := by
  refine ⟨modelo, estrutura_modelo, ⟨4 / 5, 14⟩, ⟨Or.inl (by norm_num), Or.inl rfl⟩, fun p hp h => ?_⟩
  have := (norma_primo_iff (by exact_mod_cast hp.one_lt) _).mp h
  norm_num at this

/-! ## 5. Verdadeiro, falso, ambos ou indeterminado -/

/-- **Os quatro valores**: a RH é verdadeira ou falsa; nunca as duas; e, se for falsa, a refutação é uma conta finita
(dada a equivalência de Lagarias, hipótese nomeada). Logo "indeterminado" só seria possível com a RH verdadeira. -/
theorem quatro_valores :
    (RiemannHypothesis ∨ ¬ RiemannHypothesis) ∧ ¬ (RiemannHypothesis ∧ ¬ RiemannHypothesis) ∧
    (Maquina.LagariasPi1 → (¬ RiemannHypothesis ↔ ∃ N, Maquina.maquina N = true)) :=
  ⟨em _, fun h => h.2 h.1, Maquina.refutacao_finita⟩

end ClayRiemannProof.PorQueMeio
