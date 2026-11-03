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

/-- **O par mais frágil da onda em 10¹⁴** (run 41594905434, 8 661 651 zeros em 16 janelas de 10¹⁴ com deslocamentos de
3·10¹² a 18·10¹² no índice; zeros 472 888 703 009 302 e …303, `γ ≈ 1,0103·10¹⁴`, a 0,0012132 um do outro,
`s = 0,0059`): `−9,20·10⁻⁷ ≤ λ ≤ −7,35·10⁻⁷`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV calculado: −7,3597·10⁻⁷). -/
theorem par_mais_fragil_onda_1e14 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 101033300946371831397627930412273212002114 / 10 ^ 27| ≤ 694 / 10 ^ 30)
    (h₂ : |γ₂ - 101033300946371832610851929250784856524800 / 10 ^ 27| ≤ 694 / 10 ^ 30)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(920 : ℝ) / 1000000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(735 : ℝ) / 1000000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 121322 / 100000000) (hi := 121323 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-! ## A segunda extensão: 16 faixas acima de 3 000 175 822 471,5

Runs 41632268598 (faixas 0–3) e 41652868086 (faixas 4–15), branch `resultados-continuacao`, pastas
`de_3000175822471.5/` e `de_3000175822471.5/faixas_4-15/`: 16 faixas contíguas de 120 000 unidades,
`3 000 175 822 471,5 < Im s ≤ 3 000 177 742 471,5`, 8 217 533 zeros, todos na reta, `N(T)` exato nas 17 pontas
(`N(3 000 177 742 471,5) = 12 363 163 750 447`), as 16 colagens conferindo e déficit 0 em cada faixa. Hipótese nomeada
`JanelaContinuacao2026b`. -/

/-- **Janela da segunda extensão (fora do kernel)**: todos os zeros com `3 000 175 822 471 < Im s ≤ 3 000 177 742 471`
estão na reta (a primeira extensão vai até `…822 471,5`; as faixas 0–15 vão de `…822 471,5` a `…742 471,5`). -/
def JanelaContinuacao2026b : Prop := JanelaNaReta 3000175822471 3000177742471

/-- RH até `3 000 177 742 471`, condicional a Platt–Trudgian e às três janelas da Arb. -/
theorem rhAteZ_continuacao2 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026)
    (hC2 : JanelaContinuacao2026b) : RHateZ 3000177742471 :=
  rhateZ_estende (rhAteZ_continuacao hPT hJ hC) (by exact_mod_cast hC2)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 177 742 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao2 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026)
    (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000177742471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima (rhAteZ_continuacao2 hPT hJ hC hC2) h
  simpa using this

/-- **O par mais frágil das 16 faixas** (zeros 12 363 161 233 435 e …436, `γ ≈ 3 000 177 154 379,729`, a 0,00073130 um
do outro, `s = 0,0031`): `−3,35·10⁻⁷ ≤ λ ≤ −2,67·10⁻⁷`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV calculado:
−2,6740·10⁻⁷). É o par mais perto da colisão em todos os dados. -/
theorem par_mais_fragil_continuacao2 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300017715437972941998805856576 / 10 ^ 17| ≤ 106 / 10 ^ 20)
    (h₂ : |γ₂ - 300017715437973015128376648229 / 10 ^ 17| ≤ 232 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(335 : ℝ) / 1000000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(267 : ℝ) / 1000000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 73129 / 100000000) (hi := 73130 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-! ## A terceira extensão: faixas 16–35 acima de 3 000 177 742 471,5

Runs 41675244133 (faixas 16–23) e 41690164119 (faixas 24–35), pastas `de_3000175822471.5/faixas_16-23/` e
`faixas_24-35/`; colagem conjunta das 36 faixas em `de_3000175822471.5/juntas_0-35/`: `3 000 175 822 471,5 < Im s ≤
3 000 180 142 471,5`, 18 489 450 zeros, todos na reta, as 36 colagens conferindo, déficit 0 em cada faixa,
`N(3 000 180 142 471,5) = 12 363 174 022 364`. Hipótese nomeada `JanelaContinuacao2026c` (o trecho acima de
`…742 471`). -/

/-- **Janela da terceira extensão (fora do kernel)**: todos os zeros com `3 000 177 742 471 < Im s ≤ 3 000 180 142 471`
estão na reta. -/
def JanelaContinuacao2026c : Prop := JanelaNaReta 3000177742471 3000180142471

/-- RH até `3 000 180 142 471`, condicional a Platt–Trudgian e às quatro janelas da Arb. -/
theorem rhAteZ_continuacao3 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026)
    (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c) : RHateZ 3000180142471 :=
  rhateZ_estende (rhAteZ_continuacao2 hPT hJ hC hC2) (by exact_mod_cast hC3)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 180 142 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao3 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026)
    (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c)
    (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000180142471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima (rhAteZ_continuacao3 hPT hJ hC hC2 hC3) h
  simpa using this

/-- **O par mais frágil das 36 faixas** (zeros 12 363 167 808 945 e …946, `γ ≈ 3 000 178 690 726,1623`, a 0,00061840 um
do outro, `s = 0,0026`): `−2,40·10⁻⁷ ≤ λ ≤ −1,91·10⁻⁷`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV calculado:
−1,9121·10⁻⁷). É o par mais perto da colisão em todos os dados. -/
theorem par_mais_fragil_continuacao3 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300017869072616233566825147131 / 10 ^ 17| ≤ 313 / 10 ^ 20)
    (h₂ : |γ₂ - 300017869072616295407189495341 / 10 ^ 17| ≤ 213 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(240 : ℝ) / 1000000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(191 : ℝ) / 1000000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 61840 / 100000000) (hi := 61841 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

end ClayRiemannProof.Continuacao
