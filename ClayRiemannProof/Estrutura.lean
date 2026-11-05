import ClayRiemannProof.Aurea
import ClayRiemannProof.PontesTotal
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A estrutura toda: operadores, leis, a barreira, as pontes e o que surge (§50–53 no kernel)

Este arquivo põe no kernel o que nas §50–53 ainda era conta ou fato citado, e organiza tudo como uma estrutura com
operadores e leis.

1. **Operadores** (`gira c θ`, a rotação de ângulo `θ` em torno do pivô `c`). Leis de grupo: `gira_zero`,
   `gira_soma`, `gira_volta`; isometria; meia volta `s ↦ 2c − s`; a lei diedral `espelho_gira` (o espelho conjuga a
   rotação na inversa). As rotações das §52 e §53 são casos: `gira_meio_quarto` (`rot90`), `gira_zero_oitavo` (`ωᵏ`).
2. **A estrutura abstrata** `EstruturaDeRiemann W`: tudo o que as §50–53 usaram dos zeros (faixa, `s ↦ 1 − s`,
   `s ↦ s̄`, altura acima de 13). `estrutura_Z`: os zeros de `ζ` a satisfazem.
3. **Leis gerais**, provadas para qualquer `W` com a estrutura: girar por `θ` em torno de ½ com `|sin θ| ≥ 1/13`
   tira todo ponto da faixa; em torno do 0, com `|sin θ| ≥ 2/13`. Para `ζ`: até 26 cópias em torno de ½
   (`copias_meio`) e até 13 em torno do 0 (`copias_zero`) tiram todo zero não trivial da faixa, exceto a identidade
   e (em ½) a meia volta. Ângulos: `< 1/26` dos braços, `< 1/13` dos raios; a órbita diedral nunca é um polígono
   regular para `n ≤ 40` (`nunca_regular`).
4. **A barreira** (`barreira`, `estrutura_nao_decide`): o quarteto `½ ± 3/10 ± 14i`, zeros na faixa de um polinômio com
   a mesma simetria da `ξ`, satisfaz a estrutura inteira e está fora da reta. Toda lei do item 3 vale para ele. Logo
   nenhuma prova da RH pode usar só a estrutura: falta o que `ζ` tem e o modelo não tem (o produto de Euler).
5. **As pontes geométricas** (`pontes_da_estrutura`): o enunciado do Clay equivale a "todo zero é equidistante do 0 e
   do 1", "os dois anéis da §53 coincidem", "o octeto da §52 colapsa" e "a meia volta em ½ coincide com o espelho".
   São reformulações: nenhuma é mais fraca que a RH.
6. **Densidades** (o que era fato citado): as oito cópias no 0 com `s ↦ 1 − s` geram as translações `s ↦ s + 1` e
   `s ↦ s + √2` (`translada_um`, `translada_raiz_dois`), e `ℤ + √2ℤ` é denso (`translacoes_densas`). As fases de 2 e
   3: os múltiplos de `log 2` são densos no círculo de comprimento `log 3` (`fases_densas`, Kronecker em dimensão 1).
7. **A zeta de Fibonacci** `Σ F_n^{−s}`: `F_{n+2} ≥ φⁿ`, a série converge em `Re s ≥ 1` e não tem zeros ali
   (`zetaFib_ne_zero`). Os zeros numéricos da §51 (e `σ* ≈ 0,757`) continuam conta.

Nada aqui prova RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Estrutura

open Complex ComplexConjugate ClayRiemannProof.Zeta.Symmetry ClayRiemannProof.Aurea
open scoped goldenRatio

/-! ## 1. Operadores: a rotação em torno de um pivô -/

/-- **Rotação de ângulo `θ` em torno do pivô `c`**: `s ↦ c + e^{iθ}(s − c)`. -/
noncomputable def gira (c : ℂ) (θ : ℝ) (s : ℂ) : ℂ := c + Complex.exp (θ * I) * (s - c)

theorem exp_giro (θ : ℝ) : Complex.exp (θ * I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := by
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im]
    ring
  · rw [Complex.exp_ofReal_mul_I_im]
    simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_im]
    ring

theorem gira_zero (c s : ℂ) : gira c 0 s = s := by
  simp [gira]

/-- **Lei de grupo**: girar por `θ + η` é girar por `η` e depois por `θ`. -/
theorem gira_soma (c : ℂ) (θ η : ℝ) (s : ℂ) : gira c (θ + η) s = gira c θ (gira c η s) := by
  simp only [gira, Complex.ofReal_add, add_mul, Complex.exp_add]
  ring

theorem gira_volta (c s : ℂ) : gira c (2 * Real.pi) s = s := by
  simp only [gira]
  push_cast
  rw [Complex.exp_two_pi_mul_I]
  ring

theorem gira_periodo (c : ℂ) (θ : ℝ) (s : ℂ) : gira c (θ + 2 * Real.pi) s = gira c θ s := by
  rw [gira_soma, gira_volta]

theorem gira_isometria (c : ℂ) (θ : ℝ) (s t : ℂ) : ‖gira c θ s - gira c θ t‖ = ‖s - t‖ := by
  have : gira c θ s - gira c θ t = Complex.exp (θ * I) * (s - t) := by
    simp only [gira]
    ring
  rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem gira_re (c : ℂ) (θ : ℝ) (s : ℂ) :
    (gira c θ s).re = c.re + Real.cos θ * (s - c).re - Real.sin θ * (s - c).im := by
  simp only [gira, Complex.add_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

/-- **Meia volta**: `s ↦ 2c − s`. -/
theorem gira_meia_volta (c s : ℂ) : gira c Real.pi s = 2 * c - s := by
  simp only [gira]
  rw [Complex.exp_pi_mul_I]
  ring

/-- Em torno de ½, a meia volta é a tensão `s ↦ 1 − s`, a simetria de `ζ`. -/
theorem gira_meio_meia_volta (s : ℂ) : gira (1 / 2) Real.pi s = tensao s := by
  rw [gira_meia_volta]
  simp only [tensao]
  ring

/-- A rotação de 90° da §52 é `gira ½ (π/2)`. -/
theorem gira_meio_quarto (s : ℂ) : gira (1 / 2) (Real.pi / 2) s = rot90 s := by
  simp only [gira, rot90]
  rw [exp_giro, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem exp_quarto : Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * I) = omega8 := by
  rw [exp_giro, Real.cos_pi_div_four, Real.sin_pi_div_four, omega8]
  ring

/-- As oito cópias da §53 são `gira 0 (k·π/4)`. -/
theorem gira_zero_oitavo (k : ℕ) (s : ℂ) : gira 0 (k * (Real.pi / 4)) s = omega8 ^ k * s := by
  simp only [gira, sub_zero, zero_add]
  rw [show (((k * (Real.pi / 4) : ℝ)) : ℂ) * I = (k : ℂ) * (((Real.pi / 4 : ℝ) : ℂ) * I) by push_cast; ring,
    Complex.exp_nat_mul, exp_quarto]

/-- **Lei diedral**: o espelho `s ↦ s̄` conjuga a rotação em torno de um pivô real na rotação inversa. Com as `n`
rotações de `2π/n`, isto é o grupo diedral de ordem `2n`. -/
theorem espelho_gira (c θ : ℝ) (s : ℂ) : espelho (gira c θ s) = gira c (-θ) (espelho s) := by
  have h : conj (Complex.exp (θ * I)) = Complex.exp (((-θ : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 1
    push_cast
    ring
  simp only [espelho, gira, map_add, map_mul, map_sub, Complex.conj_ofReal, h]

/-! ## 2. A estrutura abstrata -/

/-- **A estrutura de Riemann**: tudo o que as §50–53 usaram dos zeros. -/
structure EstruturaDeRiemann (W : Set ℂ) : Prop where
  faixa : ∀ ρ ∈ W, 0 < ρ.re ∧ ρ.re < 1
  fecha_tensao : ∀ ρ ∈ W, tensao ρ ∈ W
  fecha_espelho : ∀ ρ ∈ W, espelho ρ ∈ W
  altura : ∀ ρ ∈ W, 13 < |ρ.im|

/-- **Os zeros não triviais de `ζ` têm a estrutura.** -/
theorem estrutura_Z : EstruturaDeRiemann Z where
  faixa := fun _ h => ⟨h.2.1, h.2.2⟩
  fecha_tensao := fun _ h => tensao_mem_Z h
  fecha_espelho := fun _ h => espelho_mem_Z h
  altura := fun ρ h => HeightThirteen.primeiro_zero_entre.2 ρ h

theorem EstruturaDeRiemann.fecha_torcao {W : Set ℂ} (hW : EstruturaDeRiemann W) {ρ : ℂ} (hρ : ρ ∈ W) :
    torcao ρ ∈ W := by
  have e : torcao ρ = tensao (espelho ρ) := by simp [torcao, tensao, espelho]
  rw [e]
  exact hW.fecha_tensao _ (hW.fecha_espelho _ hρ)

/-! ## 3. Leis gerais (para qualquer `W` com a estrutura) -/

private theorem fora_meio {x y c s : ℝ} (hx : |x| < 1 / 2) (hy : 13 < |y|) (hc : |c| ≤ 1) (hs : 1 / 13 ≤ |s|) :
    1 / 2 < |c * x - s * y| := by
  have h1 : 1 < |s * y| := by
    rw [abs_mul]
    have := mul_le_mul_of_nonneg_right hs (abs_nonneg y)
    linarith
  have h2 : |c * x| < 1 / 2 := by
    rw [abs_mul]
    have := mul_le_mul_of_nonneg_right hc (abs_nonneg x)
    linarith
  have h3 := abs_sub_abs_le_abs_sub (s * y) (c * x)
  rw [abs_sub_comm] at h3
  linarith

private theorem fora_zero {x y c s : ℝ} (hx : |x| < 1) (hy : 13 < |y|) (hc : |c| ≤ 1) (hs : 2 / 13 ≤ |s|) :
    1 < |c * x - s * y| := by
  have h1 : 2 < |s * y| := by
    rw [abs_mul]
    have := mul_le_mul_of_nonneg_right hs (abs_nonneg y)
    linarith
  have h2 : |c * x| < 1 := by
    rw [abs_mul]
    have := mul_le_mul_of_nonneg_right hc (abs_nonneg x)
    linarith
  have h3 := abs_sub_abs_le_abs_sub (s * y) (c * x)
  rw [abs_sub_comm] at h3
  linarith

/-- **Lei geral em torno de ½**: se `|sin θ| ≥ 1/13`, girar por `θ` em torno de ½ leva todo ponto de `W` para fora
da faixa. -/
theorem EstruturaDeRiemann.gira_meio {W : Set ℂ} (hW : EstruturaDeRiemann W) {ρ : ℂ} (hρ : ρ ∈ W) {θ : ℝ}
    (hθ : 1 / 13 ≤ |Real.sin θ|) : ¬ (0 < (gira (1 / 2) θ ρ).re ∧ (gira (1 / 2) θ ρ).re < 1) := by
  obtain ⟨h0, h1⟩ := hW.faixa ρ hρ
  have hy := hW.altura ρ hρ
  rintro ⟨g0, g1⟩
  rw [gira_re] at g0 g1
  have ere : (ρ - 1 / 2).re = ρ.re - 1 / 2 := by simp
  have eim : (ρ - 1 / 2).im = ρ.im := by simp
  have ec : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  rw [ere, eim, ec] at g0 g1
  have hx : |ρ.re - 1 / 2| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith
  have := fora_meio hx hy (Real.abs_cos_le_one θ) hθ
  rcases lt_abs.mp this with h | h <;> linarith

/-- **Lei geral em torno do 0**: se `|sin θ| ≥ 2/13`, girar por `θ` em torno do 0 leva todo ponto de `W` para fora
da faixa. -/
theorem EstruturaDeRiemann.gira_zero {W : Set ℂ} (hW : EstruturaDeRiemann W) {ρ : ℂ} (hρ : ρ ∈ W) {θ : ℝ}
    (hθ : 2 / 13 ≤ |Real.sin θ|) : ¬ (0 < (gira 0 θ ρ).re ∧ (gira 0 θ ρ).re < 1) := by
  obtain ⟨h0, h1⟩ := hW.faixa ρ hρ
  have hy := hW.altura ρ hρ
  rintro ⟨g0, g1⟩
  rw [gira_re] at g0 g1
  simp only [Complex.zero_re, sub_zero, zero_add] at g0 g1
  have hx : |ρ.re| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  have := fora_zero hx hy (Real.abs_cos_le_one θ) hθ
  rcases lt_abs.mp this with h | h <;> linarith

/-- **A meia volta em torno do 0 tira todo ponto da faixa**: `−ρ` tem `−1 < Re < 0`. -/
theorem EstruturaDeRiemann.meia_volta_zero {W : Set ℂ} (hW : EstruturaDeRiemann W) {ρ : ℂ} (hρ : ρ ∈ W) :
    ¬ (0 < (gira 0 Real.pi ρ).re) := by
  rw [gira_meia_volta]
  have := (hW.faixa ρ hρ).1
  simp only [mul_zero, zero_sub, Complex.neg_re]
  linarith

/-- **Ângulo aos braços**: `arctan(|Re ρ − ½|/|Im ρ|) < 1/26` (§52, para qualquer `W` com a estrutura). -/
theorem EstruturaDeRiemann.angulo_bracos {W : Set ℂ} (hW : EstruturaDeRiemann W) {ρ : ℂ} (hρ : ρ ∈ W) :
    Real.arctan (|ρ.re - 1 / 2| / |ρ.im|) < 1 / 26 := by
  obtain ⟨h0, h1⟩ := hW.faixa ρ hρ
  have hy := hW.altura ρ hρ
  have hg : 0 < |ρ.im| := by linarith
  have hb : |ρ.re - 1 / 2| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith
  have hq : |ρ.re - 1 / 2| / |ρ.im| < 1 / 26 := by
    rw [div_lt_iff₀ hg]
    linarith
  rcases eq_or_lt_of_le (div_nonneg (abs_nonneg (ρ.re - 1 / 2)) hg.le) with h | h
  · rw [← h, Real.arctan_zero]
    norm_num
  · exact (Real.arctan_lt_self h).trans hq

/-- **Ângulo aos raios** (§53, para qualquer `W` com a estrutura): `arctan(Re ρ/|Im ρ|) < 1/13`. -/
theorem EstruturaDeRiemann.angulo_raios {W : Set ℂ} (hW : EstruturaDeRiemann W) {ρ : ℂ} (hρ : ρ ∈ W) :
    Real.arctan (ρ.re / |ρ.im|) < 1 / 13 := by
  obtain ⟨h0, h1⟩ := hW.faixa ρ hρ
  have hy := hW.altura ρ hρ
  have hg : 0 < |ρ.im| := by linarith
  have hq : ρ.re / |ρ.im| < 1 / 13 := by
    rw [div_lt_iff₀ hg]
    linarith
  exact (Real.arctan_lt_self (div_pos h0 hg)).trans hq

/-- **Nunca um polígono regular**: a órbita de um ponto fora da reta pelo grupo diedral de ordem `2n` em torno de ½
(`n` cópias giradas de `2π/n` e o espelho) são `2n` pontos em pares a `±δ` dos `2n` raios, `δ = arctan(|b|/|γ|)`; ela
só seria um `2n`-ágono regular com `δ = π/(2n)`. Como `δ < 1/26 < π/(2n)` para `n ≤ 40`, nunca é. Entram `n = 4`
(o octeto da §52) e `n = 8` (os 16 pontos da §53). -/
theorem EstruturaDeRiemann.nunca_regular {W : Set ℂ} (hW : EstruturaDeRiemann W) {ρ : ℂ} (hρ : ρ ∈ W) {n : ℕ}
    (hn : 1 ≤ n) (hn40 : n ≤ 40) : Real.arctan (|ρ.re - 1 / 2| / |ρ.im|) < Real.pi / (2 * n) := by
  refine (hW.angulo_bracos hρ).trans ?_
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn40' : (n : ℝ) ≤ 40 := by exact_mod_cast hn40
  rw [lt_div_iff₀ (by positivity)]
  linarith [Real.pi_gt_d2]

/-! ### Os ângulos que tiram os zeros: a desigualdade de Jordan -/

theorem seno_grande {θ : ℝ} (h1 : Real.pi / 26 ≤ θ) (h2 : θ ≤ Real.pi - Real.pi / 26) : 1 / 13 ≤ |Real.sin θ| := by
  have hpi := Real.pi_pos
  have key : ∀ x, Real.pi / 26 ≤ x → x ≤ Real.pi / 2 → 1 / 13 ≤ Real.sin x := by
    intro x a b
    have hj := Real.mul_le_sin (by linarith) b
    have hm : 2 / Real.pi * (Real.pi / 26) ≤ 2 / Real.pi * x := mul_le_mul_of_nonneg_left a (by positivity)
    have he : 2 / Real.pi * (Real.pi / 26) = 1 / 13 := by
      field_simp
      norm_num
    linarith
  rcases le_total θ (Real.pi / 2) with h | h
  · rw [abs_of_nonneg (by linarith [key θ h1 h])]
    exact key θ h1 h
  · have := key (Real.pi - θ) (by linarith) (by linarith)
    rw [Real.sin_pi_sub] at this
    rw [abs_of_nonneg (by linarith)]
    exact this

theorem seno_grande_zero {θ : ℝ} (h1 : Real.pi / 13 ≤ θ) (h2 : θ ≤ Real.pi - Real.pi / 13) :
    2 / 13 ≤ |Real.sin θ| := by
  have hpi := Real.pi_pos
  have key : ∀ x, Real.pi / 13 ≤ x → x ≤ Real.pi / 2 → 2 / 13 ≤ Real.sin x := by
    intro x a b
    have hj := Real.mul_le_sin (by linarith) b
    have hm : 2 / Real.pi * (Real.pi / 13) ≤ 2 / Real.pi * x := mul_le_mul_of_nonneg_left a (by positivity)
    have he : 2 / Real.pi * (Real.pi / 13) = 2 / 13 := by
      field_simp
    linarith
  rcases le_total θ (Real.pi / 2) with h | h
  · rw [abs_of_nonneg (by linarith [key θ h1 h])]
    exact key θ h1 h
  · have := key (Real.pi - θ) (by linarith) (by linarith)
    rw [Real.sin_pi_sub] at this
    rw [abs_of_nonneg (by linarith)]
    exact this

/-- **Lei geral para `ζ` em torno de ½**: girar por `θ` com `|sin θ| ≥ 1/13` tira todo zero não trivial da faixa. -/
theorem gira_meio_tira_da_faixa {ρ : ℂ} (hρ : ρ ∈ Z) {θ : ℝ} (hθ : 1 / 13 ≤ |Real.sin θ|) :
    gira (1 / 2) θ ρ ∉ Z :=
  fun h => estrutura_Z.gira_meio hρ hθ ⟨h.2.1, h.2.2⟩

/-- **Lei geral para `ζ` em torno do 0**: girar por `θ` com `|sin θ| ≥ 2/13` tira todo zero não trivial da faixa. -/
theorem gira_zero_tira_da_faixa {ρ : ℂ} (hρ : ρ ∈ Z) {θ : ℝ} (hθ : 2 / 13 ≤ |Real.sin θ|) : gira 0 θ ρ ∉ Z :=
  fun h => estrutura_Z.gira_zero hρ hθ ⟨h.2.1, h.2.2⟩

/-- **Até 26 cópias em torno de ½**: com `n ≤ 26` cópias giradas de `2π/n`, toda cópia `k` (`0 < k < n`) que não é
a meia volta (`2k ≠ n`) tira todo zero não trivial da faixa. Generaliza a §52 (`n = 4`) e o pivô ½ da §53 (`n = 8`). -/
theorem copias_meio {n k : ℕ} (hn : n ≤ 26) (hk0 : 0 < k) (hkn : k < n) (hk2 : 2 * k ≠ n) {ρ : ℂ} (hρ : ρ ∈ Z) :
    gira (1 / 2) (2 * Real.pi * k / n) ρ ∉ Z := by
  apply gira_meio_tira_da_faixa hρ
  have hpi := Real.pi_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn' : (n : ℝ) ≤ 26 := by exact_mod_cast hn
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk0
  rcases Nat.lt_or_gt_of_ne hk2 with h | h
  · have h' : (2 * k + 1 : ℝ) ≤ n := by exact_mod_cast (show 2 * k + 1 ≤ n by omega)
    apply seno_grande
    · rw [le_div_iff₀ hn0]
      nlinarith
    · rw [div_le_iff₀ hn0]
      nlinarith
  · have h' : (n + 1 : ℝ) ≤ 2 * k := by exact_mod_cast (show n + 1 ≤ 2 * k by omega)
    have h'' : (2 * k + 2 : ℝ) ≤ 2 * n := by exact_mod_cast (show 2 * k + 2 ≤ 2 * n by omega)
    have e : Real.sin (2 * Real.pi * k / n) = -Real.sin (2 * Real.pi * k / n - Real.pi) := by
      rw [Real.sin_sub_pi]
      ring
    have hd : 2 * Real.pi * k / n - Real.pi = Real.pi * (2 * k - n) / n := by
      field_simp
    have a1 := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 * k - n by linarith) hpi.le
    have a2 := mul_le_mul_of_nonneg_left hn' hpi.le
    rw [e, abs_neg]
    apply seno_grande
    · rw [hd, le_div_iff₀ hn0]
      nlinarith
    · rw [sub_le_iff_le_add, div_le_iff₀ hn0]
      nlinarith

/-- **Até 13 cópias em torno do 0**: com `n ≤ 13` cópias giradas de `2π/n` em torno do 0, toda cópia `k` com
`0 < k < n` (inclusive a meia volta) tira todo zero não trivial da faixa. Generaliza a §53 (`n = 8`). -/
theorem copias_zero {n k : ℕ} (hn : n ≤ 13) (hk0 : 0 < k) (hkn : k < n) {ρ : ℂ} (hρ : ρ ∈ Z) :
    gira 0 (2 * Real.pi * k / n) ρ ∉ Z := by
  have hpi := Real.pi_pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn' : (n : ℝ) ≤ 13 := by exact_mod_cast hn
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk0
  rcases lt_trichotomy (2 * k) n with h | h | h
  · apply gira_zero_tira_da_faixa hρ
    have h' : (2 * k + 1 : ℝ) ≤ n := by exact_mod_cast (show 2 * k + 1 ≤ n by omega)
    apply seno_grande_zero
    · rw [le_div_iff₀ hn0]
      nlinarith
    · rw [div_le_iff₀ hn0]
      nlinarith
  · have e : 2 * Real.pi * k / n = Real.pi := by
      have : (2 * k : ℝ) = n := by exact_mod_cast h
      field_simp
      linarith
    rw [e]
    intro hz
    exact estrutura_Z.meia_volta_zero hρ hz.2.1
  · apply gira_zero_tira_da_faixa hρ
    have h' : (n + 1 : ℝ) ≤ 2 * k := by exact_mod_cast (show n + 1 ≤ 2 * k by omega)
    have h'' : (2 * k + 2 : ℝ) ≤ 2 * n := by exact_mod_cast (show 2 * k + 2 ≤ 2 * n by omega)
    have e : Real.sin (2 * Real.pi * k / n) = -Real.sin (2 * Real.pi * k / n - Real.pi) := by
      rw [Real.sin_sub_pi]
      ring
    have hd : 2 * Real.pi * k / n - Real.pi = Real.pi * (2 * k - n) / n := by
      field_simp
    have a1 := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ 2 * k - n by linarith) hpi.le
    have a2 := mul_le_mul_of_nonneg_left hn' hpi.le
    rw [e, abs_neg]
    apply seno_grande_zero
    · rw [hd, le_div_iff₀ hn0]
      nlinarith
    · rw [sub_le_iff_le_add, div_le_iff₀ hn0]
      nlinarith

/-! ## 4. A barreira: a estrutura não decide a reta -/

/-- **O modelo**: o quarteto `½ ± 3/10 ± 14i`. -/
def modelo : Set ℂ := {s | (s.re = 1 / 2 + 3 / 10 ∨ s.re = 1 / 2 - 3 / 10) ∧ (s.im = 14 ∨ s.im = -14)}

theorem estrutura_modelo : EstruturaDeRiemann modelo where
  faixa := by
    rintro ρ ⟨h | h, -⟩ <;> rw [h] <;> norm_num
  fecha_tensao := by
    rintro ρ ⟨hr, hi⟩
    simp only [modelo, Set.mem_ofPred_eq, tensao, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    constructor
    · rcases hr with h | h
      · right
        rw [h]
        norm_num
      · left
        rw [h]
        norm_num
    · rcases hi with h | h
      · right
        rw [h]
        norm_num
      · left
        rw [h]
        norm_num
  fecha_espelho := by
    rintro ρ ⟨hr, hi⟩
    simp only [modelo, Set.mem_ofPred_eq, espelho, Complex.conj_re, Complex.conj_im]
    refine ⟨hr, ?_⟩
    rcases hi with h | h
    · right
      rw [h]
    · left
      rw [h]
      norm_num
  altura := by
    rintro ρ ⟨-, h | h⟩ <;> rw [h] <;> norm_num

/-- O ponto do quarteto modelo que serve de testemunha. -/
noncomputable def zModelo : ℂ := ⟨3 / 10, 14⟩

/-- **Os zeros do polinômio-quarteto são exatamente o modelo**: `quartetoPoly z (s − ½) = 0 ⟺ s ∈ modelo`. -/
theorem poly_zero_iff (s : ℂ) : Analogs.quartetoPoly zModelo (s - 1 / 2) = 0 ↔ s ∈ modelo := by
  simp only [Analogs.quartetoPoly, mul_eq_zero, modelo, Set.mem_ofPred_eq, Complex.ext_iff, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, zModelo]
  norm_num
  constructor
  · rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
    · exact ⟨Or.inl (by linarith), Or.inl (by linarith)⟩
    · exact ⟨Or.inr (by linarith), Or.inr (by linarith)⟩
    · exact ⟨Or.inl (by linarith), Or.inr (by linarith)⟩
    · exact ⟨Or.inr (by linarith), Or.inl (by linarith)⟩
  · rintro ⟨h1 | h1, h2 | h2⟩
    · exact Or.inl (Or.inl (Or.inl ⟨by linarith, by linarith⟩))
    · exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)
    · exact Or.inr ⟨by linarith, by linarith⟩
    · exact Or.inl (Or.inl (Or.inr ⟨by linarith, by linarith⟩))

/-- **A barreira**: existe `f` com a mesma simetria da `ξ` (`f(−w) = f(w)`, `f(w̄) = conj f(w)`, na coordenada
`w = s − ½`) cujos zeros na faixa têm a estrutura inteira (faixa, `1 − s`, `s̄`, altura acima de 13) e um quarteto
fora da reta. Toda lei da seção 3 vale para eles. -/
theorem barreira : ∃ f : ℂ → ℂ, Analogs.Simetrica f ∧
    EstruturaDeRiemann {s : ℂ | f (s - 1 / 2) = 0 ∧ 0 < s.re ∧ s.re < 1} ∧
    ∃ ρ : ℂ, f (ρ - 1 / 2) = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ ρ.re ≠ 1 / 2 := by
  refine ⟨Analogs.quartetoPoly zModelo, Analogs.quartetoPoly_simetrica _, ?_, ⟨⟨4 / 5, 14⟩, ?_, ?_, ?_, ?_⟩⟩
  · have e : {s : ℂ | Analogs.quartetoPoly zModelo (s - 1 / 2) = 0 ∧ 0 < s.re ∧ s.re < 1} = modelo := by
      ext s
      constructor
      · exact fun h => (poly_zero_iff s).mp h.1
      · intro h
        exact ⟨(poly_zero_iff s).mpr h, estrutura_modelo.faixa s h⟩
    rw [e]
    exact estrutura_modelo
  · exact (poly_zero_iff _).mpr ⟨Or.inl (by norm_num), Or.inl rfl⟩
  · norm_num
  · norm_num
  · norm_num

/-- **A estrutura não decide a reta**: nenhum argumento que use só a faixa, as duas simetrias e a altura acima de 13
prova a RH. -/
theorem estrutura_nao_decide : ¬ ∀ W : Set ℂ, EstruturaDeRiemann W → ∀ ρ ∈ W, ρ.re = 1 / 2 := by
  intro h
  have := h modelo estrutura_modelo ⟨4 / 5, 14⟩ ⟨Or.inl (by norm_num), Or.inl rfl⟩
  norm_num at this

/-! ## 5. As pontes geométricas -/

theorem reta_iff_equidistante (ρ : ℂ) : ρ.re = 1 / 2 ↔ ‖ρ‖ = ‖1 - ρ‖ := by
  rw [← pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, Complex.sq_norm, Complex.sq_norm,
    Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    nlinarith

theorem norma_torcao (ρ : ℂ) : ‖torcao ρ‖ = ‖1 - ρ‖ := by
  rw [torcao, ← Complex.norm_conj, map_sub, map_one, Complex.conj_conj]

theorem reta_iff_octeto (ρ : ℂ) (hρ : ρ.im ≠ 0) : ρ.re = 1 / 2 ↔ Real.arctan (|ρ.re - 1 / 2| / |ρ.im|) = 0 := by
  rw [Real.arctan_eq_zero_iff, div_eq_zero_iff, abs_eq_zero, abs_eq_zero, sub_eq_zero]
  constructor
  · exact Or.inl
  · rintro (h | h)
    · exact h
    · exact absurd h hρ

theorem reta_iff_espelho_meia_volta (ρ : ℂ) : ρ.re = 1 / 2 ↔ gira (1 / 2) Real.pi ρ = espelho ρ := by
  rw [gira_meio_meia_volta, Complex.ext_iff]
  simp only [tensao, espelho, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, Complex.conj_re,
    Complex.conj_im]
  constructor
  · intro h
    exact ⟨by linarith, by ring⟩
  · rintro ⟨h, -⟩
    linarith

/-- **As pontes da estrutura**: o enunciado do Clay equivale a cada uma das formas geométricas das §52–53. São
reformulações (nenhuma é mais fraca que a RH): fechar qualquer uma é fechar a RH.

1. Clay; 2. todo zero na reta; 3. todo zero equidistante do 0 e do 1; 4. os dois anéis da §53 coincidem
(`‖ρ‖ = ‖1 − ρ̄‖`); 5. o octeto da §52 colapsa (`δ = 0`); 6. a meia volta em ½ coincide com o espelho. -/
theorem pontes_da_estrutura : List.TFAE
    [ Target,
      ∀ ρ ∈ Z, ρ.re = 1 / 2,
      ∀ ρ ∈ Z, ‖ρ‖ = ‖1 - ρ‖,
      ∀ ρ ∈ Z, ‖ρ‖ = ‖torcao ρ‖,
      ∀ ρ ∈ Z, Real.arctan (|ρ.re - 1 / 2| / |ρ.im|) = 0,
      ∀ ρ ∈ Z, gira (1 / 2) Real.pi ρ = espelho ρ ] := by
  tfae_have 1 ↔ 2 := by
    have key : Target ↔ ∀ s ∈ Z, torcao s = s := PontesTotal.pontes_total.out 1 11
    rw [key]
    exact ⟨fun h ρ hρ => (torcao_fixo_iff ρ).mp (h ρ hρ), fun h ρ hρ => (torcao_fixo_iff ρ).mpr (h ρ hρ)⟩
  tfae_have 2 ↔ 3 := forall₂_congr fun ρ _ => reta_iff_equidistante ρ
  tfae_have 3 ↔ 4 := forall₂_congr fun ρ _ => by rw [norma_torcao]
  tfae_have 2 ↔ 5 := forall₂_congr fun ρ hρ => by
    have h13 := estrutura_Z.altura ρ hρ
    exact reta_iff_octeto ρ (fun h => by rw [h, abs_zero] at h13; norm_num at h13)
  tfae_have 2 ↔ 6 := forall₂_congr fun ρ _ => reta_iff_espelho_meia_volta ρ
  tfae_finish

/-! ## 6. Densidades: as translações e as fases -/

/-- **A translação gerada**: girar por `−θ` no 0, meia volta no 0, `s ↦ 1 − s`, girar por `θ` no 0. -/
noncomputable def translada (θ : ℝ) (s : ℂ) : ℂ := gira 0 θ (tensao (gira 0 Real.pi (gira 0 (-θ) s)))

theorem translada_eq (θ : ℝ) (s : ℂ) : translada θ s = s + Complex.exp (θ * I) := by
  have h : Complex.exp (θ * I) * Complex.exp (((-θ : ℝ) : ℂ) * I) = 1 := by
    rw [← Complex.exp_add]
    push_cast
    simp
  rw [translada, gira_meia_volta]
  simp only [tensao, gira]
  linear_combination s * h

/-- **Meia volta no 0 com a tensão é `s ↦ s + 1`.** -/
theorem translada_um (s : ℂ) : translada 0 s = s + 1 := by
  rw [translada_eq]
  simp

/-- **As cópias de ±45° com a tensão dão `s ↦ s + √2`.** -/
theorem translada_raiz_dois (s : ℂ) : translada (Real.pi / 4) (translada (-(Real.pi / 4)) s) = s + (√2 : ℝ) := by
  rw [translada_eq, translada_eq, exp_giro, exp_giro, Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  push_cast
  ring

/-- **As translações geradas são densas**: `ℤ + √2ℤ` é denso em `ℝ` (porque √2 é irracional). Um conjunto discreto e
não vazio não pode ser fechado por elas. -/
theorem translacoes_densas : Dense (AddSubgroup.closure {(1 : ℝ), √2} : Set ℝ) := by
  rw [Set.pair_comm, dense_addSubgroupClosure_pair_iff, div_one]
  exact irrational_sqrt_two

/-- **Os zeros não são fechados pela translação gerada**: `ρ + 1` sai da faixa. -/
theorem zeros_nao_transladam {ρ : ℂ} (hρ : ρ ∈ Z) : translada 0 ρ ∉ Z := by
  rw [translada_um]
  rintro ⟨-, -, h⟩
  have := hρ.2.1
  simp only [Complex.add_re, Complex.one_re] at h
  linarith

theorem log_irracional : Irrational (Real.log 2 / Real.log 3) := by
  rintro ⟨q, hq⟩
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : (0 : ℝ) < q := by
    rw [hq]
    positivity
  have hnum : 0 < q.num := Rat.num_pos.mpr (by exact_mod_cast hpos)
  apply fases_independentes q.num.toNat q.den q.den_pos
  rw [← hq, Rat.cast_def]
  congr 1
  have : ((q.num.toNat : ℕ) : ℤ) = q.num := Int.toNat_of_nonneg hnum.le
  rw [← this]
  push_cast
  rfl

/-- **As fases de 2 e 3 enchem o toro** (Kronecker em dimensão 1): os múltiplos de `log 2` são densos no círculo de
comprimento `log 3`. É a seção de Poincaré do fluxo `t ↦ (t log 2, t log 3)` no toro das fases da §50. -/
theorem fases_densas : DenseRange (fun n : ℤ => n • ((Real.log 2 : ℝ) : AddCircle (Real.log 3))) :=
  AddCircle.denseRange_zsmul_coe_iff.mpr log_irracional

/-! ## 7. A zeta de Fibonacci -/

/-- **`F_{n+2} ≥ φⁿ`** (e `F_{n+3} ≥ φⁿ⁺¹`). -/
theorem fib_ge_phi : ∀ n : ℕ, φ ^ n ≤ (Nat.fib (n + 2) : ℝ) ∧ φ ^ (n + 1) ≤ (Nat.fib (n + 3) : ℝ)
  | 0 => by
    refine ⟨by norm_num [Nat.fib_add_two], ?_⟩
    norm_num [Nat.fib_add_two]
    exact Real.goldenRatio_lt_two.le
  | n + 1 => by
    obtain ⟨h1, h2⟩ := fib_ge_phi n
    refine ⟨h2, ?_⟩
    have e : Nat.fib (n + 1 + 3) = Nat.fib (n + 2) + Nat.fib (n + 3) := by
      rw [show n + 1 + 3 = (n + 2) + 2 by ring, Nat.fib_add_two]
    have hp : φ ^ (n + 1 + 1) = φ ^ (n + 1) + φ ^ n := by
      rw [show n + 1 + 1 = n + 2 by ring, pow_add, Real.goldenRatio_sq]
      ring
    rw [e, Nat.cast_add, hp]
    linarith

/-- **A zeta de Fibonacci** `ζ_F(s) = Σ_{n≥1} F_n^{−s}` (sem produto de Euler). -/
noncomputable def zetaFib (s : ℂ) : ℂ := ∑' n : ℕ, ((Nat.fib (n + 1) : ℕ) : ℂ) ^ (-s)

theorem fib_pos (n : ℕ) : 0 < Nat.fib (n + 1) := Nat.fib_pos.mpr (Nat.succ_pos n)

theorem norma_termo {s : ℂ} (hs : 1 ≤ s.re) (n : ℕ) :
    ‖((Nat.fib (n + 1) : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / (Nat.fib (n + 1) : ℝ) := by
  rw [Complex.norm_natCast_cpow_of_pos (fib_pos n), Complex.neg_re, one_div, ← Real.rpow_neg_one]
  apply Real.rpow_le_rpow_of_exponent_le
  · exact_mod_cast fib_pos n
  · linarith

theorem termo_le_geom (n : ℕ) : 1 / (Nat.fib (n + 3) : ℝ) ≤ φ⁻¹ ^ (n + 1) := by
  rw [inv_pow, ← one_div]
  exact one_div_le_one_div_of_le (pow_pos Real.goldenRatio_pos _) (fib_ge_phi n).2

theorem termo_le_geom' (n : ℕ) : 1 / (Nat.fib (n + 1) : ℝ) ≤ φ * φ⁻¹ ^ n := by
  rcases n with _ | n
  · simp only [zero_add, Nat.fib_one, Nat.cast_one, div_one, pow_zero, mul_one]
    exact Real.one_lt_goldenRatio.le
  · have h := one_div_le_one_div_of_le (pow_pos Real.goldenRatio_pos _) (fib_ge_phi n).1
    rw [show n + 1 + 1 = n + 2 by ring]
    refine h.trans (le_of_eq ?_)
    rw [inv_pow, pow_succ, one_div]
    field_simp

theorem inv_phi_lt_one : φ⁻¹ < 1 := inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio

theorem zetaFib_summable {s : ℂ} (hs : 1 ≤ s.re) :
    Summable fun n : ℕ => ((Nat.fib (n + 1) : ℕ) : ℂ) ^ (-s) :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one (inv_nonneg.mpr Real.goldenRatio_pos.le)
    inv_phi_lt_one).mul_left φ) fun n => (norma_termo hs n).trans (termo_le_geom' n)

/-- **A zeta de Fibonacci não tem zeros em `Re s ≥ 1`**: `ζ_F(s) = 1 + 1 + Σ_{n≥3} F_n^{−s}` e a cauda tem norma
`≤ Σ_{m≥1} φ^{−m} = φ < 2`. (A §51 achou numericamente `σ* ≈ 0,757`; aqui fica a cota 1, no kernel.) -/
theorem zetaFib_ne_zero {s : ℂ} (hs : 1 ≤ s.re) : zetaFib s ≠ 0 := by
  have hsum := zetaFib_summable hs
  have hsum1 : Summable fun n : ℕ => ((Nat.fib (n + 1 + 1) : ℕ) : ℂ) ^ (-s) :=
    (summable_nat_add_iff 1).mpr hsum
  have e0 : ((Nat.fib (0 + 1) : ℕ) : ℂ) ^ (-s) = 1 := by simp
  have e1 : ((Nat.fib (0 + 1 + 1) : ℕ) : ℂ) ^ (-s) = 1 := by simp [Nat.fib_two]
  have split : zetaFib s = 1 + (1 + ∑' n : ℕ, ((Nat.fib (n + 3) : ℕ) : ℂ) ^ (-s)) := by
    unfold zetaFib
    rw [hsum.tsum_eq_zero_add, e0, hsum1.tsum_eq_zero_add, e1]
  set T := ∑' n : ℕ, ((Nat.fib (n + 3) : ℕ) : ℂ) ^ (-s) with hT
  have hgeo : Summable fun n : ℕ => φ⁻¹ ^ (n + 1) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (inv_nonneg.mpr Real.goldenRatio_pos.le)
      inv_phi_lt_one)
  have hb : ∀ n : ℕ, ‖((Nat.fib (n + 3) : ℕ) : ℂ) ^ (-s)‖ ≤ φ⁻¹ ^ (n + 1) := fun n =>
    (norma_termo hs (n + 2)).trans (termo_le_geom n)
  have hnorm : Summable fun n : ℕ => ‖((Nat.fib (n + 3) : ℕ) : ℂ) ^ (-s)‖ := hgeo.of_nonneg_of_le
    (fun _ => norm_nonneg _) hb
  have hval : ∑' n : ℕ, φ⁻¹ ^ (n + 1) = φ := by
    simp only [pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_lt_one (inv_nonneg.mpr Real.goldenRatio_pos.le) inv_phi_lt_one]
    have h2 := Real.goldenRatio_sq
    have hi : φ⁻¹ = φ - 1 := inv_eq_of_mul_eq_one_right (by linear_combination h2)
    have h3 : (2 : ℝ) - φ ≠ 0 := by linarith [Real.goldenRatio_lt_two]
    rw [hi, show (1 : ℝ) - (φ - 1) = 2 - φ by ring, inv_mul_eq_iff_eq_mul₀ h3]
    linear_combination h2
  have hTle : ‖T‖ ≤ φ := by
    calc ‖T‖ ≤ ∑' n : ℕ, ‖((Nat.fib (n + 3) : ℕ) : ℂ) ^ (-s)‖ := norm_tsum_le_tsum_norm hnorm
      _ ≤ ∑' n : ℕ, φ⁻¹ ^ (n + 1) := hnorm.tsum_le_tsum hb hgeo
      _ = φ := hval
  intro h0
  rw [split] at h0
  have hT2 : T = -2 := by linear_combination h0
  rw [hT2, norm_neg] at hTle
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2] at hTle
  linarith [Real.goldenRatio_lt_two]

end ClayRiemannProof.Estrutura
