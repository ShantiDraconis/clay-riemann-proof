import Mathlib

/-!
# Lei de Gram, blocos de Gram e a exceção de Rosser do aglomerado

Para qualquer contagem `N : ℝ → ℤ` e qualquer fase `θ` (a de Riemann–Siegel nas contas), `S(t) = N(t) − θ(t)/π − 1`.
Nos pontos de Gram (`θ(g_m) = mπ`):

* `S_gram`: `S(g_m) = N(g_m) − m − 1`, um inteiro;
* `zeros_no_bloco`: zeros entre dois pontos de Gram = comprimento do bloco + variação de `S`;
* `bloco_par`: entre dois pontos de Gram **bons** (`S(g_m)` par), zeros − comprimento é par — excesso e falta só
  aparecem de 2 em 2 (é por isso que um bloco com zeros a mais vem junto de um bloco com zeros a menos);
* `aglomerado_rosser`: o aglomerado da faixa certificada (seção 13). Com `N` nos três pontos de Gram lidos da lista da
  Arb (hipóteses), os três pontos são bons, `S = 0, 2, 0`, o bloco `[g_{…050}, g_{…051}]` (comprimento 1) tem **3**
  zeros e o bloco `[g_{…051}, g_{…053}]` (comprimento 2) tem **0**: é a exceção à regra de Rosser, com os dois zeros
  que faltam no vazio deslocados para o intervalo anterior.

Os pontos de Gram e os valores de `N` vêm da Arb, fora do kernel; o kernel confere a aritmética. Nada aqui prova ou
refuta RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Gram

open Real

/-- `S(t) = N(t) − θ(t)/π − 1`. -/
noncomputable def S (N : ℝ → ℤ) (θ : ℝ → ℝ) (t : ℝ) : ℝ := N t - θ t / π - 1

/-- **Lei de Gram**: num ponto de Gram, `S(g_m) = N(g_m) − m − 1`. -/
theorem S_gram (N : ℝ → ℤ) (θ : ℝ → ℝ) {m : ℤ} {g : ℝ} (h : θ g = m * π) :
    S N θ g = (N g : ℝ) - m - 1 := by
  unfold S
  rw [h, mul_div_assoc, div_self pi_ne_zero, mul_one]

/-- `S(g_m)` é inteiro. -/
theorem S_gram_inteiro (N : ℝ → ℤ) (θ : ℝ → ℝ) {m : ℤ} {g : ℝ} (h : θ g = m * π) :
    ∃ k : ℤ, S N θ g = k :=
  ⟨N g - m - 1, by
    rw [S_gram N θ h]
    first
      | norm_cast
      | (push_cast; ring)
      | simp⟩

/-- **Zeros num bloco de Gram = comprimento + variação de `S`.** -/
theorem zeros_no_bloco (N : ℝ → ℤ) (θ : ℝ → ℝ) {m m' : ℤ} {g g' : ℝ} (h : θ g = m * π)
    (h' : θ g' = m' * π) :
    ((N g' - N g : ℤ) : ℝ) = ((m' - m : ℤ) : ℝ) + (S N θ g' - S N θ g) := by
  rw [S_gram N θ h, S_gram N θ h']
  push_cast
  ring

/-- Ponto de Gram bom: `S(g_m)` par. -/
def Bom (N : ℝ → ℤ) (θ : ℝ → ℝ) (m : ℤ) (g : ℝ) : Prop := θ g = m * π ∧ Even (N g - m - 1)

/-- **Excesso e falta só de 2 em 2**: entre dois pontos de Gram bons, zeros − comprimento é par. -/
theorem bloco_par {N : ℝ → ℤ} {θ : ℝ → ℝ} {m m' : ℤ} {g g' : ℝ} (h : Bom N θ m g) (h' : Bom N θ m' g') :
    Even ((N g' - N g) - (m' - m)) := by
  obtain ⟨a, ha⟩ := h.2
  obtain ⟨b, hb⟩ := h'.2
  exact ⟨b - a, by omega⟩

/-- **O aglomerado e a exceção de Rosser** (`g₀ = g_{12363153449050}`, `g₁ = g_{12363153449051}`,
`g₃ = g_{12363153449053}`; `N(g₀) = 12363153449051`, `N(g₁) = N(g₃) = 12363153449054` pela lista certificada). -/
theorem aglomerado_rosser (N : ℝ → ℤ) (θ : ℝ → ℝ) {g₀ g₁ g₃ : ℝ}
    (h₀ : θ g₀ = ((12363153449050 : ℤ) : ℝ) * π) (h₁ : θ g₁ = ((12363153449051 : ℤ) : ℝ) * π)
    (h₃ : θ g₃ = ((12363153449053 : ℤ) : ℝ) * π)
    (n₀ : N g₀ = 12363153449051) (n₁ : N g₁ = 12363153449054) (n₃ : N g₃ = 12363153449054) :
    Bom N θ 12363153449050 g₀ ∧ Bom N θ 12363153449051 g₁ ∧ Bom N θ 12363153449053 g₃ ∧
      S N θ g₀ = 0 ∧ S N θ g₁ = 2 ∧ S N θ g₃ = 0 ∧
      N g₁ - N g₀ = 3 ∧ N g₃ - N g₁ = 0 := by
  refine ⟨⟨h₀, ?_⟩, ⟨h₁, ?_⟩, ⟨h₃, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [n₀]; exact ⟨0, by norm_num⟩
  · rw [n₁]; exact ⟨1, by norm_num⟩
  · rw [n₃]; exact ⟨0, by norm_num⟩
  · rw [S_gram N θ h₀]; norm_num [n₀]
  · rw [S_gram N θ h₁]; norm_num [n₁]
  · rw [S_gram N θ h₃]; norm_num [n₃]
  · norm_num [n₀, n₁]
  · norm_num [n₁, n₃]

end ClayRiemannProof.Gram
