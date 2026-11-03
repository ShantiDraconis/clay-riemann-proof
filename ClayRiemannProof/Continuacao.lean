import ClayRiemannProof.PrimeiroFora
import ClayRiemannProof.Lehmer

/-!
# A continuação contígua: RH até 3 000 175 822 471 (condicional) e o par mais frágil acima da faixa

A continuação (workflow `continuacao.yml`, run 41559243734, branch `resultados-continuacao`) certificou com a Arb
quatro faixas contíguas de 120 000 unidades acima da seção 13: `3 000 175 342 471,5 < Im s ≤ 3 000 175 822 471,5`,
2 054 383 zeros, todos na reta, `N(T)` exato nas pontas de cada faixa, as faixas colando (`N` na mesma altura igual
pelas duas) e déficit 0 em cada uma. Com a seção 13 (que vai até `…342 471,5`), a janela `(…342 471, …822 471]` é a
hipótese nomeada `JanelaContinuacao2026`.

* `rhAteZ_continuacao`: Platt–Trudgian + `JanelaArb2026` + `JanelaContinuacao2026` ⟹ RH até `3 000 175 822 471`.
* `primeiro_fora_acima_continuacao`: o primeiro zero fora da reta, se existir, tem `Im > 3 000 175 822 471`.
* `par_mais_fragil_continuacao`: o par mais próximo dos 2 milhões de zeros (índices 12 363 153 756 750 e …751, a
  0,000958 um do outro, `s = 0,0041`): `−5,75·10⁻⁷ ≤ λ ≤ −4,59·10⁻⁷` (bolas da Arb e a condição de Lehmer como
  hipóteses). É o par mais perto da colisão em todos os dados, 70 vezes mais perto de `0⁻` que o da seção 13.

As janelas e as bolas são cálculos fora do kernel (hipóteses nomeadas). Nada aqui prova ou refuta RH.
`OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Continuacao

open ClayRiemannProof.Turing ClayRiemannProof.PrimeiroFora ClayRiemannProof.FiniteWorlds
  ClayRiemannProof.Zeta.Symmetry ClayRiemannProof.Lehmer

/-- **Janela da continuação (fora do kernel)**: todos os zeros com `3 000 175 342 471 < Im s ≤ 3 000 175 822 471`
estão na reta (seção 13 até `…342 471,5`; faixas 0–3 da continuação até `…822 471,5`). Hipótese nomeada. -/
def JanelaContinuacao2026 : Prop := JanelaNaReta 3000175342471 3000175822471

/-- RH até `3 000 175 822 471`, condicional a Platt–Trudgian e às duas janelas da Arb. -/
theorem rhAteZ_continuacao (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) :
    RHateZ 3000175822471 :=
  rhateZ_estende (rhAteZ_janela hPT hJ) (by exact_mod_cast hC)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 175 822 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao (hPT : PlattTrudgian2021) (hJ : JanelaArb2026)
    (hC : JanelaContinuacao2026) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000175822471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima (rhAteZ_continuacao hPT hJ hC) h
  simpa using this

/-- **O par mais frágil da continuação** (zeros 12 363 153 756 750 e …751): `−5,75·10⁻⁷ ≤ λ ≤ −4,59·10⁻⁷`
(tempo do fluxo de de Bruijn, coordenadas `x = 2γ`), qualquer que seja `g` com `Δ²g ≤ 4/5`. -/
theorem par_mais_fragil_continuacao {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300017540747641458674825851737 / 10 ^ 17| ≤ 320 / 10 ^ 20)
    (h₂ : |γ₂ - 300017540747641554521538353087 / 10 ^ 17| ≤ 460 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(575 : ℝ) / 1000000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(459 : ℝ) / 1000000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 95846 / 100000000) (hi := 95847 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-- **O par mais frágil da 1ª onda da fronteira em 10¹⁸** (run 41557877448; zeros 6 144 758 226 908 699 989 e
…990, `γ ≈ 10¹⁸ + 3 899,320`, a 0,004024 um do outro, `s = 0,0254`): `−1,013·10⁻⁵ ≤ λ ≤ −8,09·10⁻⁶`, qualquer que
seja `g` com `Δ²g ≤ 4/5` (CSV calculado: −8,1016·10⁻⁶). -/
theorem par_mais_fragil_1e18 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 100000000000000389932032850114189286666246196551 / 10 ^ 29| ≤ 241 / 10 ^ 32)
    (h₂ : |γ₂ - 100000000000000389932435294821857057532926138729 / 10 ^ 29| ≤ 241 / 10 ^ 32)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(1013 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(809 : ℝ) / 100000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 402444 / 100000000) (hi := 402445 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-- **O par mais frágil da 2ª onda da fronteira** (run 41591657623, 7 791 406 zeros em 16 janelas de 10¹³ a 10¹⁸;
zeros 467 888 702 979 044 e …045, `γ ≈ 10¹⁴ + 13 241,144`, a 0,0010522 um do outro, `s = 0,0051`):
`−6,93·10⁻⁷ ≤ λ ≤ −5,53·10⁻⁷`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV calculado: −5,5362·10⁻⁷). -/
theorem par_mais_fragil_onda2 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 1000000000132411435990232053448527653704437 / 10 ^ 28| ≤ 781 / 10 ^ 31)
    (h₂ : |γ₂ - 1000000000132411446512723879200591795836998 / 10 ^ 28| ≤ 781 / 10 ^ 31)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(693 : ℝ) / 1000000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(553 : ℝ) / 1000000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 105224 / 100000000) (hi := 105225 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

end ClayRiemannProof.Continuacao
