import ClayRiemannProof.Nos
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# As frações de quebra: o ponto exato em que cada problema passa de um lado ao outro

Cada problema aberto tem um número, quase sempre uma fração, que separa o lado provado do lado aberto ou do lado
falso. Este arquivo põe no kernel a parte exata de cada um, com números gigantescamente pequenos e gigantes:

1. **As caudas `{γ}` em frações: a lei de Gauss–Kuzmin** (`gauss_kuzmin_produto`, `gauss_kuzmin_soma`,
   `gauss_kuzmin_primeiro`). Os dígitos de fração contínua de quase todo número real seguem
   `P(a = k) = log₂(1 + 1/(k(k + 2)))`; a soma telescopa: `Σ_{k ≤ n} P(k) = log₂(2(n + 1)/(n + 2)) < 1`. As caudas dos
   14 380 683 zeros certificados seguem essa lei (README §45): compartilham os parâmetros de quase todo número real
   (Gauss–Kuzmin, Khinchin, Lévy), não um parâmetro especial de outro problema.
2. **Beal e Fermat generalizado: a fração `χ = 1/x + 1/y + 1/z`** (`chi`, `chi_euclidianos`, `chi_esferico_235`,
   `beal_chi`, `beal_folga`, `hiperbolico_maximo`, `fermat_generalizado_gigantes`, `beal_com_fator`, `beal_mundo_10`,
   `beal_cota_C`, `beal_ate_6`). `χ > 1`: famílias infinitas; `χ = 1`: os casos euclidianos `(2,3,6), (2,4,4),
   (3,3,3)`; `χ < 1`: só finitas soluções primitivas (Darmon–Granville 1995). O maior `χ < 1` é `41/42`, em `(2,3,7)`:
   a quebra é exata, com folga mínima `1/42`. Com os três expoentes `≥ 3` (Beal), `χ ≤ 1` e a folga é `≥ 1/12`
   fora de `(3,3,3)`. As 10 soluções primitivas conhecidas com `χ < 1` (todas com um expoente 2, até
   `43⁸ + 96222³ = 30042907²`) conferidas no kernel; o mundo finito de Beal (bases `≤ 6`, expoentes 3 a 5) sem
   contraexemplo.
3. **Navier–Stokes: `2/p + 3/q`** (`serrin`, `serrin_criticos`, `energia_supercritica`, `kolmogorov`). Regularidade é
   teorema quando a solução está em `L^p_t L^q_x` com `2/p + 3/q ≤ 1` (Prodi–Serrin–Ladyzhenskaya; o extremo
   `L^∞_t L³_x` por Escauriaza–Seregin–Šverák 2003). A energia só dá `L^∞_t L²_x`, com `2/∞ + 3/2 = 3/2`: a lacuna
   entre `1` e `3/2` é o problema aberto. E o expoente de Kolmogorov `−5/3` sai da análise dimensional, resolvida no
   kernel.
4. **Yang–Mills: `β₀ = 11N/3 − 2n_f/3`** (`beta0`, `liberdade_assintotica_iff`, `qcd_beta0`, `qcd_quebra`). Liberdade
   assintótica (Gross–Wilczek–Politzer 1973) ⟺ `n_f < 11N/2`; para a QCD (`N = 3`, `n_f = 6`), `β₀ = 7 > 0`, e a
   quebra é em `n_f = 33/2`. O gap de massa continua aberto.
5. **P vs NP: o 3-SAT aleatório e o primeiro momento** (`primeiro_momento_3sat`, `primeiro_momento_justo`). O número
   esperado de soluções é `(2(7/8)^α)ⁿ`; ele vai a 0 para `α > ln 2/ln(8/7) = 5,19…`: o kernel confere
   `32·7²⁶ < 8²⁶` (`α = 26/5`) e `8²⁵⁹ < 2⁵⁰·7²⁵⁹` (`α = 259/50`), com inteiros de 234 dígitos. O limiar real é
   menor (`≈ 4,27`, medido em `computations/fracoes/sat3.py`).
6. **BSD: a fração supersingular** (`E0_ordinario_97`, `E0_metade_97`). Para `y² = x³ − x` (multiplicação complexa),
   `a_p = 0` exatamente para `p ≡ 3 (mod 4)` entre 5 e 97: 12 de 23 primos, e a fração tende a `½` (Deuring).
7. **RH: os números gigantescamente pequenos** (`defeito_no_alto`, `li_indice_no_alto`). Um zero fora da reta a
   `b = 10⁻³` na altura `3·10¹²` tem defeito do círculo `≤ 2,3·10⁻²⁸` e só aparece no critério de Li depois de
   `n ≈ 1,35·10²⁸` coeficientes.

Os teoremas publicados citados (Darmon–Granville, Prodi–Serrin, ESS, Gross–Wilczek–Politzer, Deuring) não estão
formalizados aqui; o kernel confere só a parte exata. Nada aqui resolve nenhum problema aberto. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Fracoes

/-! ## 1. As caudas em frações: Gauss–Kuzmin -/

/-- **O produto telescópico**: `∏_{k=1}^{n} (k + 1)²/(k(k + 2)) = 2(n + 1)/(n + 2)`. -/
theorem gauss_kuzmin_produto (n : ℕ) :
    ∏ k ∈ Finset.range n, (((k : ℝ) + 2) ^ 2 / (((k : ℝ) + 1) * ((k : ℝ) + 3))) = 2 * ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    push_cast
    field_simp
    ring

/-- **A soma de Gauss–Kuzmin**: `Σ_{k=1}^{n} log₂(1 + 1/(k(k + 2))) = log₂(2(n + 1)/(n + 2))`. -/
theorem gauss_kuzmin_soma (n : ℕ) :
    ∑ k ∈ Finset.range n, Real.logb 2 (1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3))) =
      Real.logb 2 (2 * ((n : ℝ) + 1) / ((n : ℝ) + 2)) := by
  have e : ∀ k : ℕ, (1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3))) = ((k : ℝ) + 2) ^ 2 / (((k : ℝ) + 1) * ((k : ℝ) + 3)) := by
    intro k
    field_simp
    ring
  simp only [e]
  rw [← gauss_kuzmin_produto n]
  unfold Real.logb
  rw [← Finset.sum_div, Real.log_prod]
  intro k _
  positivity

/-- **As probabilidades somam menos que 1 em toda etapa** (e tendem a 1). -/
theorem gauss_kuzmin_menor_que_um (n : ℕ) :
    ∑ k ∈ Finset.range n, Real.logb 2 (1 + 1 / (((k : ℝ) + 1) * ((k : ℝ) + 3))) < 1 := by
  rw [gauss_kuzmin_soma, Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity), Real.rpow_one,
    div_lt_iff₀ (by positivity)]
  linarith

/-- **`P(a = 1) = log₂(4/3)`**: o quociente parcial mais provável. -/
theorem gauss_kuzmin_primeiro : Real.logb 2 (1 + 1 / (1 * 3)) = Real.logb 2 (4 / 3) := by
  norm_num

/-! ## 2. Beal e Fermat generalizado: `χ = 1/x + 1/y + 1/z` -/

/-- `χ(x, y, z) = 1/x + 1/y + 1/z`. -/
def chi (x y z : ℕ) : ℚ := 1 / x + 1 / y + 1 / z

/-- **Os casos euclidianos** `(2, 3, 6)`, `(2, 4, 4)`, `(3, 3, 3)` têm `χ = 1`. -/
theorem chi_euclidianos : chi 2 3 6 = 1 ∧ chi 2 4 4 = 1 ∧ chi 3 3 3 = 1 := by
  unfold chi
  norm_num

/-- **O icosaédrico** `(2, 3, 5)` é esférico: `χ = 31/30 > 1`. -/
theorem chi_esferico_235 : chi 2 3 5 = 31 / 30 := by
  unfold chi
  norm_num

/-- `1/x ≤ 1/3` para `x ≥ 3`, em `ℚ`. -/
theorem inv_le_terco {x : ℕ} (hx : 3 ≤ x) : (1 : ℚ) / x ≤ 1 / 3 := by
  have : (3 : ℚ) ≤ x := by exact_mod_cast hx
  exact one_div_le_one_div_of_le (by norm_num) this

/-- **Beal está no lado hiperbólico**: com `x, y, z ≥ 3`, `χ ≤ 1`, com igualdade só em `(3, 3, 3)`. -/
theorem beal_chi {x y z : ℕ} (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    chi x y z ≤ 1 ∧ (chi x y z = 1 → x = 3 ∧ y = 3 ∧ z = 3) := by
  have h1 := inv_le_terco hx
  have h2 := inv_le_terco hy
  have h3 := inv_le_terco hz
  refine ⟨by unfold chi; linarith, fun h => ?_⟩
  unfold chi at h
  have e1 : (1 : ℚ) / x = 1 / 3 := by linarith
  have e2 : (1 : ℚ) / y = 1 / 3 := by linarith
  have e3 : (1 : ℚ) / z = 1 / 3 := by linarith
  have hx0 : (x : ℚ) ≠ 0 := by positivity
  have hy0 : (y : ℚ) ≠ 0 := by positivity
  have hz0 : (z : ℚ) ≠ 0 := by positivity
  rw [div_eq_div_iff hx0 (by norm_num)] at e1
  rw [div_eq_div_iff hy0 (by norm_num)] at e2
  rw [div_eq_div_iff hz0 (by norm_num)] at e3
  refine ⟨?_, ?_, ?_⟩ <;> [exact_mod_cast (by linarith : (x : ℚ) = 3); exact_mod_cast (by linarith : (y : ℚ) = 3);
    exact_mod_cast (by linarith : (z : ℚ) = 3)]

/-- **A folga de Beal**: com `3 ≤ x ≤ y ≤ z` e `(x, y, z) ≠ (3, 3, 3)`, `χ ≤ 11/12` (máximo em `(3, 3, 4)`). -/
theorem beal_folga {x y z : ℕ} (hx : 3 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (hne : ¬ (x = 3 ∧ y = 3 ∧ z = 3)) :
    chi x y z ≤ 11 / 12 := by
  unfold chi
  have h1 := inv_le_terco hx
  have h2 := inv_le_terco (le_trans hx hxy)
  have h3 := inv_le_terco (le_trans hx (le_trans hxy hyz))
  have hz4 : 4 ≤ z := by omega
  have h4 : (1 : ℚ) / z ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hz4)
  linarith

/-- **O maior `χ < 1` é `41/42`**, em `(2, 3, 7)` (o triângulo hiperbólico de menor área; o mesmo número da cota
de Hurwitz `84(g − 1)`): para `1 ≤ x ≤ y ≤ z` com `χ < 1`, `χ ≤ 41/42`. -/
theorem hiperbolico_maximo {x y z : ℕ} (hx : 1 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (h : chi x y z < 1) :
    chi x y z ≤ 41 / 42 := by
  unfold chi at h ⊢
  have hy1 : 1 ≤ y := le_trans hx hxy
  have hz1 : 1 ≤ z := le_trans hy1 hyz
  have hxq : (x : ℚ) ≤ y := by exact_mod_cast hxy
  have hyq : (y : ℚ) ≤ z := by exact_mod_cast hyz
  have inv_le : ∀ {a b : ℕ}, 1 ≤ a → a ≤ b → (1 : ℚ) / b ≤ 1 / a := fun {a b} ha hab =>
    one_div_le_one_div_of_le (by exact_mod_cast ha) (by exact_mod_cast hab)
  rcases (show x = 1 ∨ x = 2 ∨ x = 3 ∨ 4 ≤ x by omega) with rfl | rfl | rfl | hx4
  · -- x = 1: χ ≥ 1
    have : (0 : ℚ) < (y : ℚ)⁻¹ + (z : ℚ)⁻¹ := by positivity
    norm_num at h
    linarith
  · rcases (show y = 2 ∨ y = 3 ∨ y = 4 ∨ 5 ≤ y by omega) with rfl | rfl | rfl | hy5
    · have : (0 : ℚ) < 1 / z := by positivity
      norm_num at h
      linarith
    · -- (2, 3, z): χ < 1 ⟹ z ≥ 7
      have hz7 : 7 ≤ z := by
        by_contra hc
        push Not at hc
        interval_cases z <;> norm_num at h
      have := inv_le (by norm_num) hz7
      norm_num at this ⊢
      linarith
    · -- (2, 4, z): z ≥ 5
      have hz5 : 5 ≤ z := by
        by_contra hc
        push Not at hc
        interval_cases z
        norm_num at h
      have := inv_le (by norm_num) hz5
      norm_num at this ⊢
      linarith
    · have a := inv_le (by norm_num) hy5
      have b := inv_le (by norm_num) (le_trans hy5 hyz)
      norm_num at a b ⊢
      linarith
  · rcases (show y = 3 ∨ 4 ≤ y by omega) with rfl | hy4
    · have hz4 : 4 ≤ z := by
        by_contra hc
        push Not at hc
        interval_cases z
        norm_num at h
      have := inv_le (by norm_num) hz4
      norm_num at this ⊢
      linarith
    · have a := inv_le (by norm_num) hy4
      have b := inv_le (by norm_num) (le_trans hy4 hyz)
      norm_num at a b ⊢
      linarith
  · have a := inv_le (by norm_num) hx4
    have b := inv_le (by norm_num) (le_trans hx4 hxy)
    have c := inv_le (by norm_num) (le_trans hx4 (le_trans hxy hyz))
    norm_num at a b c ⊢
    linarith

/-- **As 10 soluções primitivas conhecidas de `Aˣ + Bʸ = Cᶻ` com `χ < 1`** (todas com um expoente 2; nenhuma é de
Beal, que pede os três `≥ 3`), conferidas no kernel. -/
theorem fermat_generalizado_gigantes :
    1 ^ 7 + 2 ^ 3 = 3 ^ 2 ∧ 2 ^ 5 + 7 ^ 2 = 3 ^ 4 ∧ 7 ^ 3 + 13 ^ 2 = 2 ^ 9 ∧ 2 ^ 7 + 17 ^ 3 = 71 ^ 2 ∧
      3 ^ 5 + 11 ^ 4 = 122 ^ 2 ∧ 17 ^ 7 + 76271 ^ 3 = 21063928 ^ 2 ∧ 1414 ^ 3 + 2213459 ^ 2 = 65 ^ 7 ∧
      9262 ^ 3 + 15312283 ^ 2 = 113 ^ 7 ∧ 43 ^ 8 + 96222 ^ 3 = 30042907 ^ 2 ∧ 33 ^ 8 + 1549034 ^ 2 = 15613 ^ 3 := by
  norm_num

/-- **Os `χ` dessas soluções**: `41/42`, `19/20`, `17/18`, `23/24` (todas `< 1`). -/
theorem chi_das_gigantes :
    chi 7 3 2 = 41 / 42 ∧ chi 5 2 4 = 19 / 20 ∧ chi 3 2 9 = 17 / 18 ∧ chi 8 3 2 = 23 / 24 := by
  unfold chi
  norm_num

/-- **Beal com fator comum** (permitido): `2³ + 2³ = 2⁴`, `3³ + 6³ = 3⁵`, `7³ + 7⁴ = 14³`, `2⁹ + 8³ = 4⁵`,
`3⁹ + 54³ = 3¹¹`. -/
theorem beal_com_fator :
    2 ^ 3 + 2 ^ 3 = 2 ^ 4 ∧ 3 ^ 3 + 6 ^ 3 = 3 ^ 5 ∧ 7 ^ 3 + 7 ^ 4 = 14 ^ 3 ∧ 2 ^ 9 + 8 ^ 3 = 4 ^ 5 ∧
      3 ^ 9 + 54 ^ 3 = 3 ^ 11 := by
  norm_num

/-- **O mundo finito de Beal** (bases `A, B ≤ 6`, `C < 25`, expoentes 3, 4, 5): toda solução tem fator comum. -/
theorem beal_mundo_6 :
    ∀ A ∈ List.range' 1 6, ∀ B ∈ List.range' 1 6, ∀ C ∈ List.range' 1 24, ∀ x ∈ [3, 4, 5], ∀ y ∈ [3, 4, 5],
      ∀ z ∈ [3, 4, 5], A ^ x + B ^ y = C ^ z → 1 < Nat.gcd (Nat.gcd A B) C := by
  decide +kernel

/-- **Fora de `C < 25` não há solução** nesse mundo: `Aˣ + Bʸ ≤ 2·6⁵ = 15 552 < 25³ = 15 625 ≤ Cᶻ`. -/
theorem beal_cota_C {A B C x y z : ℕ} (hA : A ≤ 6) (hB : B ≤ 6) (hx : x ≤ 5) (hy : y ≤ 5) (hz : 3 ≤ z)
    (hC : 25 ≤ C) : A ^ x + B ^ y < C ^ z := by
  have h1 : A ^ x ≤ 6 ^ 5 :=
    le_trans (Nat.pow_le_pow_left hA x) (Nat.pow_le_pow_right (by norm_num) hx)
  have h2 : B ^ y ≤ 6 ^ 5 :=
    le_trans (Nat.pow_le_pow_left hB y) (Nat.pow_le_pow_right (by norm_num) hy)
  have h3 : 25 ^ 3 ≤ C ^ z :=
    le_trans (Nat.pow_le_pow_left hC 3) (Nat.pow_le_pow_right (by omega) hz)
  have : 2 * 6 ^ 5 < 25 ^ 3 := by norm_num
  omega

/-- **Beal no mundo das bases até 6**: para `1 ≤ A, B ≤ 6`, expoentes em `{3, 4, 5}` e qualquer `C`,
`Aˣ + Bʸ = Cᶻ` obriga fator comum. -/
theorem beal_ate_6 {A B C x y z : ℕ} (hA1 : 1 ≤ A) (hA : A ≤ 6) (hB1 : 1 ≤ B) (hB : B ≤ 6) (hC1 : 1 ≤ C)
    (hx : x ∈ [3, 4, 5]) (hy : y ∈ [3, 4, 5]) (hz : z ∈ [3, 4, 5]) (h : A ^ x + B ^ y = C ^ z) :
    1 < Nat.gcd (Nat.gcd A B) C := by
  have hx5 : x ≤ 5 := by simp at hx; omega
  have hy5 : y ≤ 5 := by simp at hy; omega
  have hz3 : 3 ≤ z := by simp at hz; omega
  by_cases hC : 25 ≤ C
  · exact absurd h (beal_cota_C hA hB hx5 hy5 hz3 hC).ne
  · exact beal_mundo_6 A (List.mem_range'_1.mpr ⟨hA1, by omega⟩) B (List.mem_range'_1.mpr ⟨hB1, by omega⟩)
      C (List.mem_range'_1.mpr ⟨hC1, by omega⟩) x hx y hy z hz h

/-! ## 3. Navier–Stokes: `2/p + 3/q` -/

/-- O índice de Prodi–Serrin `2/p + 3/q` de `L^p_t L^q_x`. -/
def serrin (p q : ℚ) : ℚ := 2 / p + 3 / q

/-- **Classes críticas** (`= 1`): `L⁵_{t,x}`, `L⁴_t L⁶_x`, `L⁸_t L⁴_x`. -/
theorem serrin_criticos : serrin 5 5 = 1 ∧ serrin 4 6 = 1 ∧ serrin 8 4 = 1 := by
  unfold serrin
  norm_num

/-- **A energia é supercrítica**: `L^∞_t L²_x` tem índice `0 + 3/2 = 3/2 > 1`; e `L^∞_t L³_x` (ESS 2003) tem `1`. -/
theorem energia_supercritica : (0 : ℚ) + 3 / 2 = 3 / 2 ∧ (1 : ℚ) < 3 / 2 ∧ (0 : ℚ) + 3 / 3 = 1 := by
  norm_num

/-- **Kolmogorov por análise dimensional**: `E(k) = C ε^a k^b` com `[E] = L³T⁻²`, `[ε] = L²T⁻³`, `[k] = L⁻¹` obriga
`a = 2/3` e `b = −5/3`. -/
theorem kolmogorov (a b : ℚ) : (2 * a - b = 3 ∧ -3 * a = -2) ↔ (a = 2 / 3 ∧ b = -5 / 3) := by
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨rfl, rfl⟩
    norm_num

/-! ## 4. Yang–Mills: `β₀ = 11N/3 − 2n_f/3` -/

/-- O primeiro coeficiente da função β de `SU(N)` com `n_f` férmions de Dirac na fundamental. -/
def beta0 (N nf : ℚ) : ℚ := 11 * N / 3 - 2 * nf / 3

/-- **Liberdade assintótica ⟺ `n_f < 11N/2`.** -/
theorem liberdade_assintotica_iff (N nf : ℚ) : 0 < beta0 N nf ↔ nf < 11 * N / 2 := by
  unfold beta0
  constructor <;> intro h <;> linarith

/-- **A QCD** (`N = 3`, `n_f = 6`): `β₀ = 7`. -/
theorem qcd_beta0 : beta0 3 6 = 7 := by
  unfold beta0
  norm_num

/-- **A quebra da QCD é em `n_f = 33/2`**: 16 sabores ainda são assintoticamente livres, 17 não. -/
theorem qcd_quebra : beta0 3 (33 / 2) = 0 ∧ 0 < beta0 3 16 ∧ beta0 3 17 < 0 := by
  unfold beta0
  norm_num

/-! ## 5. P vs NP: o primeiro momento do 3-SAT aleatório -/

/-- **`α = 26/5`**: `(2(7/8)^{26/5})⁵ = 32·7²⁶/8²⁶ < 1`, então o número esperado de soluções vai a 0. -/
theorem primeiro_momento_3sat : 32 * 7 ^ 26 < 8 ^ 26 := by
  norm_num

set_option exponentiation.threshold 300 in
/-- **A cota do primeiro momento é justa**: em `α = 259/50 = 5,18`, `(2(7/8)^α)⁵⁰ = 2⁵⁰·7²⁵⁹/8²⁵⁹ > 1` (inteiros de
234 dígitos). O limiar do primeiro momento está em `(5,18; 5,2)`. -/
theorem primeiro_momento_justo : 8 ^ 259 < 2 ^ 50 * 7 ^ 259 := by
  norm_num

/-! ## 6. BSD: a fração supersingular -/

/-- **`E₀: y² = x³ − x`**: `a_p ≠ 0` para `p ≡ 1 (mod 4)`, `5 ≤ p ≤ 97` (com `Maquina.E0_supersingular_97`, `a_p = 0`
exatamente para `p ≡ 3`). -/
theorem E0_ordinario_97 : ∀ p ∈ Maquina.primos97, p % 4 = 1 → Geometrias.traco p (p - 1) 0 ≠ 0 := by
  decide +kernel

/-- **A fração supersingular entre 5 e 97 é `12/23`** (tende a `½`, Deuring). -/
theorem E0_metade_97 :
    (Maquina.primos97.filter (fun p => p % 4 = 3)).length = 12 ∧ Maquina.primos97.length = 23 := by
  decide +kernel

/-! ## 7. RH: os números gigantescamente pequenos -/

/-- **O defeito de um zero fora a `b = 10⁻³` na altura `3·10¹²`** é `≤ 2b/γ² < 3·10⁻²⁸`. -/
theorem defeito_no_alto : (2 * (1 / 1000) : ℚ) / (3 * 10 ^ 12) ^ 2 < 3 / 10 ^ 28 := by
  norm_num

/-- **E o índice de Li em que ele apareceria**: `3γ²/(2b) = 1,35·10²⁸`. -/
theorem li_indice_no_alto : (3 * (3 * 10 ^ 12) ^ 2 : ℚ) / (2 * (1 / 1000)) = 135 * 10 ^ 26 := by
  norm_num

end ClayRiemannProof.Fracoes
