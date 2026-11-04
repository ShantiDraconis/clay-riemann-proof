import ClayRiemannProof.LiCircle
import ClayRiemannProof.Fronteira.Ht

/-!
# A identidade da prova, a identidade da refutação, e uma tendendo para a outra

1. **As duas identidades, num número só** (`defeito_circulo`, `defeito_espelho`, `target_iff_defeito_zero`,
   `nao_target_iff`). Para todo `ρ ≠ 0`:

       1 − |1 − 1/ρ|² = (2 Re ρ − 1)/|ρ|².

   A prova é "o defeito é 0 em todo zero" (RH ⟺ `∀ ρ ∈ Z, 1 − |1 − 1/ρ|² = 0`); a refutação é "existe um zero com
   `Re ρ < ½`", e para ele `|1 − 1/ρ|² = 1 + 2b/|ρ|²` com `b = ½ − Re ρ > 0` (pela torção, um zero com `Re ρ > ½`
   traz o espelho `1 − ρ̄` com `Re < ½`).
2. **A ponte quantitativa: quando a refutação aparece** (`li_aparece`, `li_aparece_para_zero`). Se `|w|² ≥ 1 + δ`,
   então `|wⁿ| ≥ 2` para todo `n ≥ 3/δ` (Bernoulli). Para o zero acima, `δ = 2b/|ρ|²`: a partir de
   `n ≥ 3|ρ|²/(2b) ≈ 1,5·γ²/b` o termo de Li do quarteto passa de 2 em módulo, e algum `λ_n` do quarteto fica negativo
   (`LiCircle.liQ_neg`). Um zero fora a altura `γ` só aparece no critério de Li depois de `~γ²/b` coeficientes.
3. **A refutação tendendo à prova** (`defeito_tende_a_zero`, `defeito_some_na_altura`, `familia_simetrica`,
   `colisao_no_circulo`). Com `ρ_b = ½ + b + iγ` o defeito `2b/|ρ_b|²` vai a 0 quando `b → 0`, e fica `≤ 2b/γ²` na
   altura `γ`: a refutação se apaga continuamente e fica invisível no alto. O segmento `A + tB` entre uma função do
   lado da prova e uma do lado da refutação conserva as duas simetrias para todo `t` real; a transição é um zero duplo
   sobre a reta (no círculo, `1 − 2√q·u + qu² = (1 − √q·u)²`). Os números: `computations/parametro/homotopia.py`
   segue os 13 pares fora da reta de Epstein `m² + 5n²` (`t = 1`) até a reta, na família
   `ζ·L(χ₋₂₀) + t·L(χ₋₄)L(χ₅)` que termina na zeta de Dedekind de `Q(√−5)` (`t = 0`); README §42.
4. **Refutações finitas e assintóticas** (`Robin1984`, `Lagarias2002`, `VonKoch1901`, `MertensRH`, `robin_refuta`,
   `lagarias_refuta`, `vonKoch_refuta`, `mertens_refuta`, `lambda_positivo_refuta`). Robin e Lagarias são enunciados
   nomeados (teoremas publicados, nunca `axiom`) cujo contraexemplo é **um número** `n`: uma refutação seria um
   certificado finito. Von Koch (`ψ(x) − x`) e Mertens (`M(x)`) pedem uma família infinita de violações sem cota: um
   valor grande isolado não refuta nada (a conjectura forte de Mertens `|M(x)| < √x` é falsa, Odlyzko–te Riele 1985,
   e a RH continua aberta). `Λ > 0` refutaria, com `RH_iff_Lambda`.

Nada aqui prova ou refuta RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Identidades

open Complex ComplexConjugate ClayRiemannProof.Zeta.Symmetry ClayRiemannProof.LiCircle

/-! ## 1. As duas identidades -/

/-- **A identidade do defeito**: `1 − |1 − 1/ρ|² = (2 Re ρ − 1)/|ρ|²`. -/
theorem defeito_circulo {ρ : ℂ} (h0 : ρ ≠ 0) : 1 - normSq (mob ρ) = (2 * ρ.re - 1) / normSq ρ := by
  have hn : normSq ρ ≠ 0 := (normSq_pos.mpr h0).ne'
  have h := normSq_sub_one_sub ρ
  rw [mob_eq h0, normSq_div, eq_div_iff hn, sub_mul, div_mul_cancel₀ _ hn]
  linarith

/-- **A identidade da refutação**: um zero com `Re ρ = ½ − b` tem `|1 − 1/ρ|² = 1 + 2b/|ρ|²`. -/
theorem defeito_espelho {ρ : ℂ} (h0 : ρ ≠ 0) {b : ℝ} (hb : ρ.re = 1 / 2 - b) :
    normSq (mob ρ) = 1 + 2 * b / normSq ρ := by
  have h := defeito_circulo h0
  rw [hb] at h
  have e : (2 * (1 / 2 - b) - 1) / normSq ρ = -(2 * b / normSq ρ) := by ring
  rw [e] at h
  linarith

/-- **A identidade da prova**: a meta ⟺ o defeito é 0 em todo zero. -/
theorem target_iff_defeito_zero : Target ↔ ∀ ρ ∈ Z, 1 - normSq (mob ρ) = 0 := by
  rw [target_iff_circulo]
  exact forall₂_congr fun ρ _ => ⟨fun h => by rw [h]; ring, fun h => by linarith⟩

/-- **A refutação ⟺ existe zero com `Re ρ < ½`** (a torção leva `Re > ½` em `Re < ½`). -/
theorem nao_target_iff : ¬ Target ↔ ∃ ρ ∈ Z, ρ.re < 1 / 2 := by
  rw [target_iff_circulo]
  constructor
  · intro h
    push Not at h
    obtain ⟨ρ, hρ, hne⟩ := h
    have h0 := ne_zero_of_mem_Z hρ
    have hre : ρ.re ≠ 1 / 2 := fun e => hne ((normSq_mob_eq_one_iff h0).mpr e)
    rcases lt_or_gt_of_ne hre with hlt | hgt
    · exact ⟨ρ, hρ, hlt⟩
    · refine ⟨torcao ρ, torcao_mem_Z hρ, ?_⟩
      simp only [torcao, sub_re, one_re, conj_re]
      linarith
  · rintro ⟨ρ, hρ, hlt⟩ h
    have h0 := ne_zero_of_mem_Z hρ
    have := (normSq_mob_eq_one_iff h0).mp (h ρ hρ)
    linarith

/-! ## 2. A ponte quantitativa: quando a refutação aparece no critério de Li -/

/-- **Bernoulli**: `|w|² ≥ 1 + δ` (`δ > 0`) ⟹ `|wⁿ|² ≥ 4` para todo `n ≥ 3/δ`. -/
theorem li_aparece {w : ℂ} {δ : ℝ} (hδ : 0 < δ) (hw : 1 + δ ≤ normSq w) {n : ℕ} (hn : 3 / δ ≤ n) :
    4 ≤ normSq (w ^ n) := by
  rw [map_pow]
  have h1 : (1 + δ) ^ n ≤ normSq w ^ n := pow_le_pow_left₀ (by linarith) hw n
  have h2 : 1 + n * δ ≤ (1 + δ) ^ n := one_add_mul_le_pow (by linarith) n
  have h3 : 3 ≤ n * δ := by rwa [div_le_iff₀ hδ] at hn
  linarith

/-- **Para um zero fora da reta** (`Re ρ = ½ − b`, `b > 0`): a partir de `n ≥ 3|ρ|²/(2b)`, `|(1 − 1/ρ)ⁿ| ≥ 2`; e
algum termo de Li do quarteto é negativo. -/
theorem li_aparece_para_zero {ρ : ℂ} (hρ : ρ ∈ Z) {b : ℝ} (hb0 : 0 < b) (hb : ρ.re = 1 / 2 - b) :
    (∀ n : ℕ, 3 * normSq ρ / (2 * b) ≤ n → 4 ≤ normSq (mob ρ ^ n)) ∧ ∃ n : ℕ, liQ (mob ρ) n < 0 := by
  have h0 := ne_zero_of_mem_Z hρ
  have hn0 : 0 < normSq ρ := normSq_pos.mpr h0
  have hd : 0 < 2 * b / normSq ρ := div_pos (by linarith) hn0
  have hw : 1 + 2 * b / normSq ρ ≤ normSq (mob ρ) := (defeito_espelho h0 hb).ge
  refine ⟨fun n hn => li_aparece hd hw (by rwa [div_div_eq_mul_div]), ?_⟩
  apply liQ_neg
  rw [← sq_lt_sq₀ zero_le_one (norm_nonneg _), one_pow, ← normSq_eq_norm_sq]
  linarith

/-! ## 3. A refutação tendendo à prova -/

/-- **O defeito vai a 0 com o resíduo**: `2b/((½ + b)² + γ²) → 0` quando `b → 0`. -/
theorem defeito_tende_a_zero (γ : ℝ) :
    Filter.Tendsto (fun b : ℝ => 2 * b / ((1 / 2 + b) ^ 2 + γ ^ 2)) (nhds 0) (nhds 0) := by
  have hc : ContinuousAt (fun b : ℝ => 2 * b / ((1 / 2 + b) ^ 2 + γ ^ 2)) 0 :=
    ContinuousAt.div (f := fun b : ℝ => 2 * b) (g := fun b : ℝ => (1 / 2 + b) ^ 2 + γ ^ 2) (by fun_prop)
      (by fun_prop) (by show (1 / 2 + (0 : ℝ)) ^ 2 + γ ^ 2 ≠ 0; positivity)
  simpa using hc.tendsto

/-- **No alto o defeito some**: `2b/((½ + b)² + γ²) ≤ 2b/γ²`. -/
theorem defeito_some_na_altura {b γ : ℝ} (hb : 0 ≤ b) (hγ : γ ≠ 0) :
    2 * b / ((1 / 2 + b) ^ 2 + γ ^ 2) ≤ 2 * b / γ ^ 2 :=
  div_le_div_of_nonneg_left (by linarith) (by positivity) (by nlinarith [sq_nonneg (1 / 2 + b)])

/-- **O segmento entre prova e refutação conserva as simetrias**: `A`, `B` simétricas ⟹ `A + tB` simétrica para
todo `t` real. -/
theorem familia_simetrica {A B : ℂ → ℂ} (hA : Analogs.Simetrica A) (hB : Analogs.Simetrica B) (t : ℝ) :
    Analogs.Simetrica (fun w => A w + (t : ℂ) * B w) := by
  refine ⟨fun w => by simp only [hA.1 w, hB.1 w], fun w => ?_⟩
  simp only [map_add, map_mul, conj_ofReal, hA.2 w, hB.2 w]

/-- **A transição é um zero duplo no círculo**: `1 − 2√q·u + qu² = (1 − √q·u)²`. -/
theorem colisao_no_circulo {q : ℝ} (hq : 0 ≤ q) (u : ℂ) :
    1 - ((2 * Real.sqrt q : ℝ) : ℂ) * u + (q : ℂ) * u ^ 2 = (1 - (Real.sqrt q : ℂ) * u) ^ 2 := by
  have hs : ((Real.sqrt q : ℝ) : ℂ) ^ 2 = (q : ℂ) := by rw [← ofReal_pow, Real.sq_sqrt hq]
  push_cast
  linear_combination (-u ^ 2) * hs

/-! ## 4. Refutações finitas e assintóticas -/

/-- `ψ(x) = Σ_{n ≤ x} Λ(n)` (Chebyshev). -/
noncomputable def psi (x : ℕ) : ℝ := ∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n

/-- `M(x) = Σ_{n ≤ x} μ(n)` (Mertens). -/
def mertens (x : ℕ) : ℤ := ∑ n ∈ Finset.Icc 1 x, ArithmeticFunction.moebius n

/-- **Robin (1984)** — enunciado nomeado: RH ⟺ `σ(n) < e^γ n log log n` para todo `n > 5040`. -/
def Robin1984 : Prop :=
  RiemannHypothesis ↔ ∀ n : ℕ, 5040 < n →
    (ArithmeticFunction.sigma 1 n : ℝ) < Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n)

/-- **Lagarias (2002)** — enunciado nomeado: RH ⟺ `σ(n) ≤ H_n + e^{H_n} log H_n` para todo `n ≥ 1`. -/
def Lagarias2002 : Prop :=
  RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n →
    (ArithmeticFunction.sigma 1 n : ℝ) ≤ (harmonic n : ℝ) + Real.exp (harmonic n) * Real.log (harmonic n)

/-- **von Koch (1901)** — enunciado nomeado: RH ⟺ `|ψ(x) − x| ≤ C√x log²x`. -/
def VonKoch1901 : Prop :=
  RiemannHypothesis ↔ ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x → |psi x - x| ≤ C * Real.sqrt x * Real.log x ^ 2

/-- **Mertens–Littlewood** — enunciado nomeado: RH ⟺ `M(x) = O(x^{½+ε})` para todo `ε > 0`. -/
def MertensRH : Prop :=
  RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℕ, 1 ≤ x → |(mertens x : ℝ)| ≤ C * (x : ℝ) ^ (1 / 2 + ε)

/-- **Um único `n > 5040` refuta** (com Robin). -/
theorem robin_refuta (h : Robin1984) {n : ℕ} (hn : 5040 < n)
    (hv : Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) ≤ ArithmeticFunction.sigma 1 n) :
    ¬ RiemannHypothesis := fun hRH => absurd (h.mp hRH n hn) (not_lt.mpr hv)

/-- **Um único `n ≥ 1` refuta** (com Lagarias). -/
theorem lagarias_refuta (h : Lagarias2002) {n : ℕ} (hn : 1 ≤ n)
    (hv : (harmonic n : ℝ) + Real.exp (harmonic n) * Real.log (harmonic n) < ArithmeticFunction.sigma 1 n) :
    ¬ RiemannHypothesis := fun hRH => absurd (h.mp hRH n hn) (not_le.mpr hv)

/-- **Com von Koch, refutar pede violações sem cota** (para todo `C` um `x`), não um valor grande isolado. -/
theorem vonKoch_refuta (h : VonKoch1901)
    (hv : ∀ C : ℝ, ∃ x : ℕ, 2 ≤ x ∧ C * Real.sqrt x * Real.log x ^ 2 < |psi x - x|) : ¬ RiemannHypothesis := by
  intro hRH
  obtain ⟨C, hC⟩ := h.mp hRH
  obtain ⟨x, hx, hlt⟩ := hv C
  exact absurd (hC x hx) (not_le.mpr hlt)

/-- **Com Mertens, idem**: um `ε > 0` e, para todo `C`, um `x` acima de `Cx^{½+ε}`. -/
theorem mertens_refuta (h : MertensRH) {ε : ℝ} (hε : 0 < ε)
    (hv : ∀ C : ℝ, ∃ x : ℕ, 1 ≤ x ∧ C * (x : ℝ) ^ (1 / 2 + ε) < |(mertens x : ℝ)|) : ¬ RiemannHypothesis := by
  intro hRH
  obtain ⟨C, hC⟩ := h.mp hRH ε hε
  obtain ⟨x, hx, hlt⟩ := hv C
  exact absurd (hC x hx) (not_le.mpr hlt)

/-- **`Λ > 0` refuta** (com de Bruijn–Newman, `RH ⟺ Λ ≤ 0`). -/
theorem lambda_positivo_refuta (h : Fronteira.RH_iff_Lambda) (hΛ : 0 < Fronteira.deBruijnNewman) :
    ¬ RiemannHypothesis := fun hRH => absurd (h.mp hRH) (not_le.mpr hΛ)

end ClayRiemannProof.Identidades
