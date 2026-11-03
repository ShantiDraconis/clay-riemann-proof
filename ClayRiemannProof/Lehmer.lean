import Mathlib

/-!
# Pares de Lehmer: a cota de Csordas–Smith–Varga e a lei da colisão

`csv Δ g = ((1 − (5/4)Δ²g)^{4/5} − 1)/(8g)` é a cota inferior de Csordas–Smith–Varga (1994) para a constante de
de Bruijn–Newman `Λ` que um par de zeros de `H₀` dá: `Δ` é a distância do par e
`g = Σ_{j ≠ k, k+1} 1/(x_k − x_j)² + 1/(x_{k+1} − x_j)²` a soma dos vizinhos, nas coordenadas `x = 2γ` de
`H₀(z) = ξ(½ + iz/2)/8`. O teorema de CSV (`Λ ≥ csv Δ g` para todo par com `Δ²g < 4/5`) fica fora do kernel. O que
o kernel prova sobre a cota:

* `csv_le_isolado`, `csv_ge`: para `Δ²g ≤ 4/5`, `−(5/32)Δ² ≤ csv Δ g ≤ −Δ²/8`. A cota de cima é o tempo de colisão
  do par isolado (`Colisao.colisao`); os vizinhos só empurram a cota para baixo.
* `csv_neg`: a cota é sempre negativa (`Δ ≠ 0`): nenhum par de Lehmer dá `λ ≥ 0`.
* `csv_limite`: quando os vizinhos somem (`g → 0⁺`), `csv Δ g → −Δ²/8`: a cota de CSV vira a lei da colisão.
* `csv_escala`, `csv_x_de_gamma`: em coordenadas `x = c·γ`, a cota multiplica por `c²`; de `γ` para `x = 2γ`, por 4.
  O tempo do fluxo de de Bruijn é o das coordenadas `x`; um `λ` calculado com as distâncias em `γ` sai 4 vezes menor.
* `aglomerado_052_053`, `par_mais_fragil`: os dois pares da faixa certificada da seção 13, com as bolas da Arb como
  hipóteses (`|γ − centro| ≤ raio`) e a condição de Lehmer `Δ²g ≤ 4/5` como hipótese (o `g` calculado fora do kernel
  é 57,67 e 22,35; o limite é 200,8 e 3 135):
  `−6,23·10⁻⁴ ≤ λ ≤ −4,98·10⁻⁴` no aglomerado e `−3,99·10⁻⁵ ≤ λ ≤ −3,18·10⁻⁵` no par mais frágil, qualquer que
  seja `g`.

Nada aqui prova ou refuta RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Lehmer

open Real Filter Topology Set

/-- **Cota de Csordas–Smith–Varga** de um par à distância `Δ` com soma de vizinhos `g` (coordenadas `x = 2γ`). -/
noncomputable def csv (Δ g : ℝ) : ℝ := ((1 - 5 / 4 * (Δ ^ 2 * g)) ^ (4 / 5 : ℝ) - 1) / (8 * g)

/-- Bernoulli côncavo: `(1 − u)^{4/5} ≤ 1 − (4/5)u` para `0 ≤ u ≤ 1` (média geométrica ponderada). -/
theorem bernoulli_quatro_quintos {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    (1 - u) ^ (4 / 5 : ℝ) ≤ 1 - 4 / 5 * u := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := 4 / 5) (w₂ := 1 / 5) (p₁ := 1 - u) (p₂ := 1)
    (by norm_num) (by norm_num) (by linarith) (by norm_num) (by norm_num)
  rw [Real.one_rpow, mul_one] at h
  linarith

/-- `(1 − u)^{4/5} ≥ 1 − u` para `0 ≤ u ≤ 1`: a potência `4/5 < 1` fica acima da reta em `[0, 1]`. -/
theorem acima_da_reta {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : 1 - u ≤ (1 - u) ^ (4 / 5 : ℝ) := by
  have hx0 : 0 ≤ 1 - u := by linarith
  have hx1 : 1 - u ≤ 1 := by linarith
  rcases hx0.eq_or_lt with h | h
  · rw [← h]
    positivity
  · calc 1 - u = (1 - u) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (1 - u) ^ (4 / 5 : ℝ) := by
        first
          | exact Real.rpow_le_rpow_of_exponent_ge h hx1 (by norm_num)
          | exact Real.rpow_le_rpow_of_exponent_ge' hx0 hx1 (by norm_num) (by norm_num)
          | (rw [Real.rpow_one]; exact Real.self_le_rpow_of_le_one hx0 hx1 (by norm_num))

/-- **Cota de cima: a colisão do par isolado.** Para `Δ²g ≤ 4/5`, `csv Δ g ≤ −Δ²/8`. -/
theorem csv_le_isolado {Δ g : ℝ} (hg : 0 < g) (hq : Δ ^ 2 * g ≤ 4 / 5) : csv Δ g ≤ -(Δ ^ 2) / 8 := by
  have hu0 : 0 ≤ 5 / 4 * (Δ ^ 2 * g) := by positivity
  have hb := bernoulli_quatro_quintos hu0 (by linarith)
  have h1 : (1 - 5 / 4 * (Δ ^ 2 * g)) ^ (4 / 5 : ℝ) - 1 ≤ -(Δ ^ 2 * g) := by linarith
  have h8 : (0 : ℝ) < 8 * g := by positivity
  calc csv Δ g = ((1 - 5 / 4 * (Δ ^ 2 * g)) ^ (4 / 5 : ℝ) - 1) / (8 * g) := rfl
    _ ≤ -(Δ ^ 2 * g) / (8 * g) := by gcongr
    _ = -(Δ ^ 2) / 8 := by
      first
        | rw [neg_div, neg_div, mul_div_mul_right _ _ hg.ne']
        | (field_simp; ring)
        | field_simp

/-- **Cota de baixo.** Para `Δ²g ≤ 4/5`, `csv Δ g ≥ −(5/32)Δ²`. -/
theorem csv_ge {Δ g : ℝ} (hg : 0 < g) (hq : Δ ^ 2 * g ≤ 4 / 5) : -(5 / 32 * Δ ^ 2) ≤ csv Δ g := by
  have hu0 : 0 ≤ 5 / 4 * (Δ ^ 2 * g) := by positivity
  have hb := acima_da_reta hu0 (by linarith)
  have h1 : -(5 / 4 * (Δ ^ 2 * g)) ≤ (1 - 5 / 4 * (Δ ^ 2 * g)) ^ (4 / 5 : ℝ) - 1 := by linarith
  have h8 : (0 : ℝ) < 8 * g := by positivity
  calc -(5 / 32 * Δ ^ 2) = -(5 / 4 * (Δ ^ 2 * g)) / (8 * g) := by
        rw [eq_div_iff h8.ne']
        ring
    _ ≤ ((1 - 5 / 4 * (Δ ^ 2 * g)) ^ (4 / 5 : ℝ) - 1) / (8 * g) := by gcongr
    _ = csv Δ g := rfl

/-- **Nenhum par de Lehmer dá `λ ≥ 0`**: a cota é negativa sempre que `Δ ≠ 0`. -/
theorem csv_neg {Δ g : ℝ} (hΔ : Δ ≠ 0) (hg : 0 < g) (hq : Δ ^ 2 * g ≤ 4 / 5) : csv Δ g < 0 := by
  have h2 : 0 < Δ ^ 2 := lt_of_le_of_ne (sq_nonneg Δ) (Ne.symm (pow_ne_zero 2 hΔ))
  linarith [csv_le_isolado hg hq]

/-- **Mudança de escala**: em coordenadas `x = c·γ` (distâncias vezes `c`, `g` dividido por `c²`), a cota multiplica
por `c²`. -/
theorem csv_escala {c Δ g : ℝ} (hc : c ≠ 0) : csv (c * Δ) (g / c ^ 2) = c ^ 2 * csv Δ g := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  have hq : (c * Δ) ^ 2 * (g / c ^ 2) = Δ ^ 2 * g := by
    calc (c * Δ) ^ 2 * (g / c ^ 2) = Δ ^ 2 * g * (c ^ 2 / c ^ 2) := by ring
      _ = Δ ^ 2 * g := by rw [div_self hc2, mul_one]
  unfold csv
  rw [hq]
  have h8 : 8 * (g / c ^ 2) = 8 * g / c ^ 2 := by ring
  rw [h8, div_div_eq_mul_div]
  ring

/-- **De `γ` para `x = 2γ`**: a cota multiplica por 4. -/
theorem csv_x_de_gamma (Δ g : ℝ) : csv (2 * Δ) (g / 4) = 4 * csv Δ g := by
  have h := csv_escala (c := 2) (Δ := Δ) (g := g) two_ne_zero
  have e : (2 : ℝ) ^ 2 = 4 := by norm_num
  rw [e] at h
  exact h

/-- **A cota de CSV vira a lei da colisão quando os vizinhos somem**: `csv Δ g → −Δ²/8` com `g → 0⁺`. -/
theorem csv_limite (Δ : ℝ) : Tendsto (fun g => csv Δ g) (𝓝[>] 0) (𝓝 (-(Δ ^ 2) / 8)) := by
  have hlin : HasDerivAt (fun g : ℝ => 1 - 5 / 4 * (Δ ^ 2 * g)) (-(5 / 4 * Δ ^ 2)) 0 := by
    have h := (((hasDerivAt_id' (0 : ℝ)).const_mul (Δ ^ 2)).const_mul (5 / 4 : ℝ)).const_sub (1 : ℝ)
    convert h using 1
    ring
  have hd : HasDerivAt (fun g : ℝ => (1 - 5 / 4 * (Δ ^ 2 * g)) ^ (4 / 5 : ℝ)) (-(Δ ^ 2)) 0 := by
    have h := hlin.rpow_const (p := 4 / 5) (Or.inl (by norm_num))
    convert h using 1
    first
      | (simp only [mul_zero, sub_zero, Real.one_rpow, mul_one]; ring)
      | (norm_num <;> ring)
  have hs := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono _ fun x (hx : 0 < x) => Set.mem_compl_singleton_iff.mpr (ne_of_gt hx))
  have h8 := hs.div_const 8
  refine Tendsto.congr' ?_ h8
  filter_upwards [self_mem_nhdsWithin] with g _
  rw [slope_def_field]
  simp only [csv, mul_zero, sub_zero, Real.one_rpow]
  ring

/-! ## Os dois pares da faixa certificada (seção 13) -/

/-- Diferença de dois números dados por bolas `|γ − c| ≤ r`. -/
theorem dif_bolas {γ₁ γ₂ c₁ c₂ r₁ r₂ : ℝ} (h₁ : |γ₁ - c₁| ≤ r₁) (h₂ : |γ₂ - c₂| ≤ r₂) :
    (c₂ - c₁) - (r₁ + r₂) ≤ γ₂ - γ₁ ∧ γ₂ - γ₁ ≤ (c₂ - c₁) + (r₁ + r₂) := by
  rw [abs_le] at h₁ h₂
  constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]

/-- **A faixa de `λ` só pela distância**: `lo ≤ δ ≤ hi` (`δ = γ₂ − γ₁`, `Δ = 2δ`) dá
`−(5/8)hi² ≤ csv (2δ) g ≤ −lo²/2`, qualquer que seja `g > 0` com `Δ²g ≤ 4/5`. -/
theorem csv_por_distancia {δ lo hi g : ℝ} (hlo0 : 0 ≤ lo) (hlo : lo ≤ δ) (hhi : δ ≤ hi) (hg : 0 < g)
    (hq : (2 * δ) ^ 2 * g ≤ 4 / 5) :
    -(5 / 8 * hi ^ 2) ≤ csv (2 * δ) g ∧ csv (2 * δ) g ≤ -(lo ^ 2) / 2 := by
  have a1 : lo ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hlo0 hlo 2
  have a2 : δ ^ 2 ≤ hi ^ 2 := pow_le_pow_left₀ (hlo0.trans hlo) hhi 2
  refine ⟨le_trans ?_ (csv_ge hg hq), le_trans (csv_le_isolado hg hq) ?_⟩ <;> nlinarith

/-- **O aglomerado** (zeros 12 363 153 449 052 e …053, a 0,0316 um do outro, dentro do intervalo de Gram
`[g_{12363153449050}, g_{12363153449051})` com três zeros): com as bolas da Arb,
`−6,23·10⁻⁴ ≤ λ ≤ −4,98·10⁻⁴` (tempo do fluxo de de Bruijn, coordenadas `x = 2γ`). -/
theorem aglomerado_052_053 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300017533558373280729971883801 / 10 ^ 17| ≤ 584 / 10 ^ 21)
    (h₂ : |γ₂ - 300017533558376436819517732586 / 10 ^ 17| ≤ 345 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(623 : ℝ) / 1000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(498 : ℝ) / 1000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 3156089 / 100000000) (hi := 3156090 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-- **O par mais frágil da faixa** (zeros 12 363 153 465 694 e …695, `s = 0,0342`): com as bolas da Arb,
`−3,99·10⁻⁵ ≤ λ ≤ −3,18·10⁻⁵`. -/
theorem par_mais_fragil {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300017533947204988880139519933 / 10 ^ 17| ≤ 989 / 10 ^ 21)
    (h₂ : |γ₂ - 300017533947205787582987839861 / 10 ^ 17| ≤ 315 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(399 : ℝ) / 10000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(318 : ℝ) / 10000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 798702 / 100000000) (hi := 798703 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

end ClayRiemannProof.Lehmer
