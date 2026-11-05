import ClayRiemannProof.Proporcao
import Mathlib.NumberTheory.LSeries.HardyZ

/-!
# Por que ½: o que π, Euler, `i`, ½ e 0 provam, e o que não provam

As explicações de por que os zeros têm parte real ½, provadas onde são teoremas:

1. **π, Euler, `i` e ½ fazem o espelho, e o conjunto fixo do espelho é a reta**: `½ + e^{iπ}(s − ½) = 1 − s` (a meia
   volta é a equação funcional, `euler_meia_volta`), e `s ↦ ½ + e^{iπ}(s̄ − ½) = 1 − s̄` fixa exatamente `Re s = ½`
   (`espelho_de_euler`). O 0 e o 1 são as bordas da faixa, e `Re s = ½` é onde `|s| = |1 − s|`
   (`Estrutura.reta_iff_equidistante`).
2. **Na reta, as duas metades de `ζ` pesam igual**: `|n^{−s}| = |n^{−(1−s)}|` se e só se `Re s = ½`
   (`equilibrio_dos_termos`), e `|ζ(1 − s)| = |ζ(s)|` na reta (`equilibrio_na_reta`).
3. **Um zero na reta é uma troca de sinal de uma função real, e isso é robusto**: se a função `Z` de Hardy (Mathlib)
   muda de sinal, há um zero na reta (`troca_de_sinal`); e qualquer perturbação menor que `|Z|` nas pontas ainda zera
   (`troca_de_sinal_robusta`).

E o que **não** se prova com esses ingredientes:

4. **Não é impossível sair da reta só com π, Euler, `i`, ½ e 0** (`ingredientes_nao_bastam`): `f = ξ·P`, com
   `ξ = π^{−s/2}Γ(s/2)ζ(s)` e `P` o polinômio-quarteto `±(3/10 ± 14i)`, tem a mesma simetria da `ξ`, todos os zeros
   da `ξ`, e mais um quarteto fora da reta. O que `ζ` tem e `f` não tem é ser um produto de Euler (vezes o fator
   gama): é dali que o "sempre", se for verdade, tem de vir.

Nada aqui prova RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Meio

open Complex ComplexConjugate ClayRiemannProof.Zeta.Symmetry ClayRiemannProof.Estrutura

/-! ## 1. π, Euler, `i` e ½ fazem o espelho -/

/-- **Euler faz a meia volta**: `½ + e^{iπ}(s − ½) = 1 − s`. Girar de π em torno de ½ é a simetria da equação
funcional. -/
theorem euler_meia_volta (s : ℂ) : 1 / 2 + Complex.exp (Real.pi * I) * (s - 1 / 2) = 1 - s := by
  rw [Complex.exp_pi_mul_I]
  ring

/-- **O espelho de Euler fixa exatamente a reta**: `½ + e^{iπ}(s̄ − ½) = s ⟺ Re s = ½`. -/
theorem espelho_de_euler (s : ℂ) :
    1 / 2 + Complex.exp (Real.pi * I) * (conj s - 1 / 2) = s ↔ s.re = 1 / 2 := by
  have e : 1 / 2 + Complex.exp (Real.pi * I) * (conj s - 1 / 2) = torcao s := by
    rw [Complex.exp_pi_mul_I, torcao]
    ring
  rw [e]
  exact torcao_fixo_iff s

/-! ## 2. O equilíbrio das duas metades -/

/-- **Os termos pesam igual só na reta**: para `n ≥ 2`, `|n^{−s}| = |n^{−(1−s)}| ⟺ Re s = ½`. O primeiro é o termo
da série de `ζ(s)`, o segundo o da sua imagem pela equação funcional. -/
theorem equilibrio_dos_termos {n : ℕ} (hn : 2 ≤ n) (s : ℂ) :
    ‖(n : ℂ) ^ (-s)‖ = ‖(n : ℂ) ^ (-(1 - s))‖ ↔ s.re = 1 / 2 := by
  have hn0 : 0 < n := by omega
  rw [Complex.norm_natCast_cpow_of_pos hn0, Complex.norm_natCast_cpow_of_pos hn0]
  simp only [Complex.neg_re, Complex.sub_re, Complex.one_re]
  have h1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  constructor
  · intro h
    have e : -s.re = -(1 - s.re) :=
      le_antisymm ((Real.rpow_le_rpow_left_iff h1).mp h.le) ((Real.rpow_le_rpow_left_iff h1).mp h.ge)
    linarith
  · intro h
    rw [h]
    norm_num

/-- **Na reta, `ζ` e o seu espelho têm o mesmo tamanho**: `|ζ(1 − s)| = |ζ(s)|` em `Re s = ½`, porque ali
`1 − s = s̄`. Fora da reta, o fator `|χ(s)| ≈ (t/2π)^{½−σ}` da equação funcional desequilibra as duas metades. -/
theorem equilibrio_na_reta {s : ℂ} (hs : s.re = 1 / 2) : ‖riemannZeta (1 - s)‖ = ‖riemannZeta s‖ := by
  have e : 1 - s = conj s := by
    apply Complex.ext
    · rw [Complex.sub_re, Complex.one_re, Complex.conj_re, hs]
      norm_num
    · rw [Complex.sub_im, Complex.one_im, Complex.conj_im]
      ring
  rw [e, riemannZeta_conj, Complex.norm_conj]

/-! ## 3. Um zero na reta é uma troca de sinal, e é robusto -/

theorem ivt_sinal {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ} (hab : a ≤ b) (h : f a * f b < 0) :
    ∃ t ∈ Set.Icc a b, f t = 0 := by
  have hc := hf.continuousOn (s := Set.Icc a b)
  have ha0 : f a ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    exact lt_irrefl _ h
  rcases lt_or_gt_of_ne ha0 with ha | ha
  · have hb : 0 < f b := by nlinarith
    obtain ⟨t, ht, h0⟩ := intermediate_value_Icc hab hc ⟨ha.le, hb.le⟩
    exact ⟨t, ht, h0⟩
  · have hb : f b < 0 := by nlinarith
    obtain ⟨t, ht, h0⟩ := intermediate_value_Icc' hab hc ⟨hb.le, ha.le⟩
    exact ⟨t, ht, h0⟩

/-- **Um zero na reta é uma troca de sinal**: se `Z` (a função real de Hardy) muda de sinal em `[a, b]`, `ζ` tem um
zero em `½ + it` com `t ∈ [a, b]`. -/
theorem troca_de_sinal {a b : ℝ} (hab : a ≤ b) (h : hardyZ a * hardyZ b < 0) :
    ∃ t ∈ Set.Icc a b, riemannZeta (1 / 2 + t * I) = 0 := by
  obtain ⟨t, ht, h0⟩ := ivt_sinal continuous_hardyZ hab h
  exact ⟨t, ht, (hardyZ_eq_zero_iff t).mp h0⟩

/-- **E a troca de sinal é robusta**: toda `g` contínua que difere de `Z` menos que `|Z|` nas pontas também zera em
`[a, b]`. Uma perturbação pequena que preserve a simetria (e portanto mantenha a função real na reta) não tira da reta
um zero que é troca de sinal. -/
theorem troca_de_sinal_robusta {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (hab : a ≤ b)
    (h : hardyZ a * hardyZ b < 0) (ha : |g a - hardyZ a| < |hardyZ a|) (hb : |g b - hardyZ b| < |hardyZ b|) :
    ∃ t ∈ Set.Icc a b, g t = 0 := by
  apply ivt_sinal hg hab
  have sa : 0 < g a * hardyZ a := by
    rcases lt_or_gt_of_ne (show hardyZ a ≠ 0 by intro h0; rw [h0, zero_mul] at h; exact lt_irrefl _ h) with z | z
    · rw [abs_of_neg z] at ha
      have := (abs_lt.mp ha).2
      nlinarith
    · rw [abs_of_pos z] at ha
      have := (abs_lt.mp ha).1
      nlinarith
  have sb : 0 < g b * hardyZ b := by
    rcases lt_or_gt_of_ne (show hardyZ b ≠ 0 by intro h0; rw [h0, mul_zero] at h; exact lt_irrefl _ h) with z | z
    · rw [abs_of_neg z] at hb
      have := (abs_lt.mp hb).2
      nlinarith
    · rw [abs_of_pos z] at hb
      have := (abs_lt.mp hb).1
      nlinarith
  have hp : 0 < (g a * hardyZ a) * (g b * hardyZ b) := mul_pos sa sb
  by_contra hn
  push Not at hn
  have : (g a * hardyZ a) * (g b * hardyZ b) = (g a * g b) * (hardyZ a * hardyZ b) := by ring
  nlinarith

/-! ## 4. O que esses ingredientes não provam -/

theorem simetrica_mul {f g : ℂ → ℂ} (hf : Analogs.Simetrica f) (hg : Analogs.Simetrica g) :
    Analogs.Simetrica (fun w => f w * g w) :=
  ⟨fun w => by simp only [hf.1, hg.1], fun w => by simp only [hf.2, hg.2, map_mul]⟩

/-- **π, Euler, `i`, ½ e 0 não bastam**: `f = ξ·P` (na coordenada `w = s − ½`), com `ξ(½ + w) = Λ(½ + w)`, a zeta
completada `π^{−s/2}Γ(s/2)ζ(s)`, e `P` o polinômio-quarteto `±(3/10 ± 14i)`, tem a mesma simetria da `ξ`
(`f(−w) = f(w)`, `f(w̄) = conj f(w)`), todos os zeros da `ξ`, e mais um quarteto fora da reta (`Re w ≠ 0`). -/
theorem ingredientes_nao_bastam : ∃ f : ℂ → ℂ, Analogs.Simetrica f ∧ (∀ w, Analogs.xiW w = 0 → f w = 0) ∧
    ∃ w : ℂ, f w = 0 ∧ w.re ≠ 0 := by
  refine ⟨fun w => Analogs.xiW w * Analogs.quartetoPoly zModelo w,
    simetrica_mul Analogs.xi_simetrica (Analogs.quartetoPoly_simetrica _), fun w h => by simp [h], zModelo, ?_, ?_⟩
  · simp [Analogs.quartetoPoly]
  · show (3 / 10 : ℝ) ≠ 0
    norm_num

/-- **O resumo**: o espelho feito de π, Euler, `i` e ½ fixa exatamente a reta; na reta as duas metades de `ζ` pesam
igual; e mesmo assim esses ingredientes, com a simetria inteira, admitem zeros fora da reta. -/
theorem por_que_meio :
    (∀ s : ℂ, 1 / 2 + Complex.exp (Real.pi * I) * (conj s - 1 / 2) = s ↔ s.re = 1 / 2) ∧
    (∀ s : ℂ, s.re = 1 / 2 → ‖riemannZeta (1 - s)‖ = ‖riemannZeta s‖) ∧
    (∃ f : ℂ → ℂ, Analogs.Simetrica f ∧ (∀ w, Analogs.xiW w = 0 → f w = 0) ∧ ∃ w : ℂ, f w = 0 ∧ w.re ≠ 0) :=
  ⟨espelho_de_euler, fun _ hs => equilibrio_na_reta hs, ingredientes_nao_bastam⟩

end ClayRiemannProof.Meio
