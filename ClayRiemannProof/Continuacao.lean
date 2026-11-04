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

/-! ## A quarta extensão: faixas 36–44 acima de 3 000 180 142 471,5

Run 41709096981 (faixas 36–44), pasta `de_3000175822471.5/faixas_36-44/`; colagem conjunta das 45 faixas em
`de_3000175822471.5/juntas_0-44/`: `3 000 175 822 471,5 < Im s ≤ 3 000 181 222 471,5`, 23 111 813 zeros, todos na
reta, as 45 colagens conferindo, déficit 0 em cada faixa, `N(3 000 181 222 471,5) = 12 363 178 644 727`. Hipótese
nomeada `JanelaContinuacao2026d` (o trecho acima de `…142 471`). -/

/-- **Janela da quarta extensão (fora do kernel)**: todos os zeros com `3 000 180 142 471 < Im s ≤ 3 000 181 222 471`
estão na reta. -/
def JanelaContinuacao2026d : Prop := JanelaNaReta 3000180142471 3000181222471

/-- RH até `3 000 181 222 471`, condicional a Platt–Trudgian e às cinco janelas da Arb. -/
theorem rhAteZ_continuacao4 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026)
    (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) :
    RHateZ 3000181222471 :=
  rhateZ_estende (rhAteZ_continuacao3 hPT hJ hC hC2 hC3) (by exact_mod_cast hC4)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 181 222 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao4 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026)
    (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c)
    (hC4 : JanelaContinuacao2026d) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000181222471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima (rhAteZ_continuacao4 hPT hJ hC hC2 hC3 hC4) h
  simpa using this

/-- **O par mais frágil das faixas 36–44** (zeros 12 363 175 635 090 e …091, `γ ≈ 3 000 180 519 279,4651`, a
0,0016675 um do outro, `s = 0,0071`): `−1,74·10⁻⁶ ≤ λ ≤ −1,39·10⁻⁶`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −1,3903·10⁻⁶). O par mais frágil das 45 faixas continua o de `par_mais_fragil_continuacao3`. -/
theorem par_mais_fragil_continuacao4 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300018051927946511944262498325 / 10 ^ 17| ≤ 285 / 10 ^ 20)
    (h₂ : |γ₂ - 300018051927946678691400506282 / 10 ^ 17| ≤ 449 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(174 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(139 : ℝ) / 100000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 166747 / 100000000) (hi := 166748 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-! ## A quinta extensão: faixas 0–5 acima de 3 000 181 222 471,5

Run 41749059161 (faixas 0–5 do `C0 = 3 000 181 222 471,5`), pasta `de_3000181222471.5/faixas_0-5/`; colagem em
`de_3000181222471.5/juntas_0-5/`: `3 000 181 222 471,5 < Im s ≤ 3 000 181 942 471,5`, 3 081 576 zeros, todos na reta,
as 6 colagens conferindo (a faixa 0 começa em `N(C0) = 12 363 178 644 727`, o fim da quarta extensão), déficit 0,
`N(3 000 181 942 471,5) = 12 363 181 726 303`. Hipótese nomeada `JanelaContinuacao2026e`. -/

/-- **Janela da quinta extensão (fora do kernel)**: todos os zeros com `3 000 181 222 471 < Im s ≤ 3 000 181 942 471`
estão na reta. -/
def JanelaContinuacao2026e : Prop := JanelaNaReta 3000181222471 3000181942471

/-- RH até `3 000 181 942 471`, condicional a Platt–Trudgian e às seis janelas da Arb. -/
theorem rhAteZ_continuacao5 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026)
    (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d)
    (hC5 : JanelaContinuacao2026e) : RHateZ 3000181942471 :=
  rhateZ_estende (rhAteZ_continuacao4 hPT hJ hC hC2 hC3 hC4) (by exact_mod_cast hC5)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 181 942 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao5 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026)
    (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c)
    (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000181942471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima (rhAteZ_continuacao5 hPT hJ hC hC2 hC3 hC4 hC5) h
  simpa using this

/-- **O par mais frágil das faixas 0–5 do C0 novo** (zeros 12 363 179 255 965 e …966, `γ ≈ 3 000 181 365 285,2845`,
a 0,0018293 um do outro, `s = 0,0078`): `−2,10·10⁻⁶ ≤ λ ≤ −1,67·10⁻⁶`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −1,6732·10⁻⁶). -/
theorem par_mais_fragil_continuacao5 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300018136528528453703154094549 / 10 ^ 17| ≤ 516 / 10 ^ 21)
    (h₂ : |γ₂ - 300018136528528636629535666598 / 10 ^ 17| ≤ 481 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(210 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(167 : ℝ) / 100000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 182926 / 100000000) (hi := 182927 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-! ### Sexta e sétima extensões: faixas 6–11 e 12–17 do mesmo C0

Runs 41777848348 (faixas 6, 7, 9, 10, 11), 41809658688 (faixa 8, refeita sozinha) e 41809668823 (faixas 12–17), pastas
`de_3000181222471.5/faixas_6-11/`, `faixas_8-8/` e `faixas_12-17/`; colagem das 18 faixas do `C0` em
`de_3000181222471.5/juntas_0-17/`: as 18 colagens conferem, déficit 0 em todas,
`3 000 181 222 471,5 < Im s ≤ 3 000 183 382 471,5` com 9 244 726 zeros, todos na reta (maior raio 5,01·10⁻¹⁸).
Faixas 6–11: `N` de 12 363 181 726 303 a 12 363 184 807 878 (3 081 575 zeros). Faixas 12–17: `N` de
12 363 184 807 878 a 12 363 187 889 453 (3 081 575 zeros). Hipóteses nomeadas `JanelaContinuacao2026f` e
`JanelaContinuacao2026g`. -/

/-- **Janela da sexta extensão (fora do kernel)**: todos os zeros com `3 000 181 942 471 < Im s ≤ 3 000 182 662 471`
estão na reta. -/
def JanelaContinuacao2026f : Prop := JanelaNaReta 3000181942471 3000182662471

/-- **Janela da sétima extensão (fora do kernel)**: todos os zeros com `3 000 182 662 471 < Im s ≤ 3 000 183 382 471`
estão na reta. -/
def JanelaContinuacao2026g : Prop := JanelaNaReta 3000182662471 3000183382471

/-- RH até `3 000 182 662 471`, condicional a Platt–Trudgian e às sete janelas da Arb. -/
theorem rhAteZ_continuacao6 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026)
    (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d)
    (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f) : RHateZ 3000182662471 :=
  rhateZ_estende (rhAteZ_continuacao5 hPT hJ hC hC2 hC3 hC4 hC5) (by exact_mod_cast hC6)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 182 662 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao6 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026)
    (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c)
    (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f)
    (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000182662471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima (rhAteZ_continuacao6 hPT hJ hC hC2 hC3 hC4 hC5 hC6) h
  simpa using this

/-- **O par mais frágil das faixas 6–11** (zeros 12 363 184 245 937 e …938, `γ ≈ 3 000 182 531 175,8239`, a
0,0016305 um do outro, `s = 0,0070`): `−1,67·10⁻⁶ ≤ λ ≤ −1,32·10⁻⁶`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −1,3293·10⁻⁶). -/
theorem par_mais_fragil_continuacao6 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300018253117582388296899503791 / 10 ^ 17| ≤ 592 / 10 ^ 21)
    (h₂ : |γ₂ - 300018253117582551345810876516 / 10 ^ 17| ≤ 412 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(167 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(132 : ℝ) / 100000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 163048 / 100000000) (hi := 163049 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-- RH até `3 000 183 382 471`, condicional a Platt–Trudgian e às oito janelas da Arb. -/
theorem rhAteZ_continuacao7 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026)
    (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d)
    (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) :
    RHateZ 3000183382471 :=
  rhateZ_estende (rhAteZ_continuacao6 hPT hJ hC hC2 hC3 hC4 hC5 hC6) (by exact_mod_cast hC7)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 183 382 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao7 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026)
    (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c)
    (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f)
    (hC7 : JanelaContinuacao2026g) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000183382471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima (rhAteZ_continuacao7 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7) h
  simpa using this

/-- **O par mais frágil das faixas 12–17** (zeros 12 363 185 811 880 e …881, `γ ≈ 3 000 182 897 053,2848`, a
0,0011731 um do outro, `s = 0,0050`): `−8,61·10⁻⁷ ≤ λ ≤ −6,88·10⁻⁷`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −6,8807·10⁻⁷). -/
theorem par_mais_fragil_continuacao7 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300018289705328479514937659959 / 10 ^ 17| ≤ 437 / 10 ^ 20)
    (h₂ : |γ₂ - 300018289705328596822560291128 / 10 ^ 17| ≤ 342 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(861 : ℝ) / 1000000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(688 : ℝ) / 1000000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 117307 / 100000000) (hi := 117308 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-! ### Oitava e nona extensões: faixas 0–5 e 6–11 do C0 3 000 183 382 471,5

Runs 41842620648 (faixas 0–5) e 41842633223 (faixas 6–11), pastas `de_3000183382471.5/faixas_0-5/` e `faixas_6-11/`;
colagem das 12 faixas em `de_3000183382471.5/juntas_0-11/`: as 12 colagens conferem (a faixa 0 recalcula
`N(3 000 183 382 471,5) = 12 363 187 889 453`, o fim da sétima extensão), déficit 0 em todas,
`3 000 183 382 471,5 < Im s ≤ 3 000 184 822 471,5` com 6 163 151 zeros, todos na reta (maior raio 5,01·10⁻¹⁸).
Faixas 0–5: `N` de 12 363 187 889 453 a 12 363 190 971 028 (3 081 575 zeros). Faixas 6–11: `N` de 12 363 190 971 028 a
12 363 194 052 604 (3 081 576 zeros). Hipóteses nomeadas `JanelaContinuacao2026h` e `JanelaContinuacao2026i`. -/

/-- **Janela da oitava extensão (fora do kernel)**: todos os zeros com `3 000 183 382 471 < Im s ≤ 3 000 184 102 471`
estão na reta. -/
def JanelaContinuacao2026h : Prop := JanelaNaReta 3000183382471 3000184102471

/-- **Janela da nona extensão (fora do kernel)**: todos os zeros com `3 000 184 102 471 < Im s ≤ 3 000 184 822 471`
estão na reta. -/
def JanelaContinuacao2026i : Prop := JanelaNaReta 3000184102471 3000184822471

/-- RH até `3 000 184 102 471`, condicional a Platt–Trudgian e às nove janelas da Arb. -/
theorem rhAteZ_continuacao8 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026)
    (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d)
    (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g)
    (hC8 : JanelaContinuacao2026h) : RHateZ 3000184102471 :=
  rhateZ_estende (rhAteZ_continuacao7 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7) (by exact_mod_cast hC8)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 184 102 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao8 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026)
    (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c)
    (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f)
    (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000184102471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima (rhAteZ_continuacao8 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8) h
  simpa using this

/-- **O par mais frágil das faixas 0–5, e o mais perto da colisão em todos os dados certificados até aqui** (zeros
12 363 187 982 787 e …788, `γ ≈ 3 000 183 404 278,7579`, a 0,00036432 um do outro, `s = 0,0016`):
`−8,30·10⁻⁸ ≤ λ ≤ −6,63·10⁻⁸`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV calculado: −6,6364·10⁻⁸). -/
theorem par_mais_fragil_continuacao8 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300018340427875788041891393358 / 10 ^ 17| ≤ 265 / 10 ^ 20)
    (h₂ : |γ₂ - 300018340427875824473724310148 / 10 ^ 17| ≤ 379 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(830 : ℝ) / 10000000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(663 : ℝ) / 10000000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 36431 / 100000000) (hi := 36432 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-- RH até `3 000 184 822 471`, condicional a Platt–Trudgian e às dez janelas da Arb. -/
theorem rhAteZ_continuacao9 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026)
    (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d)
    (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g)
    (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i) : RHateZ 3000184822471 :=
  rhateZ_estende (rhAteZ_continuacao8 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8) (by exact_mod_cast hC9)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 184 822 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao9 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026)
    (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c)
    (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f)
    (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i)
    (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000184822471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima (rhAteZ_continuacao9 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9) h
  simpa using this

/-- **O par mais frágil das faixas 6–11** (zeros 12 363 193 959 653 e …654, `γ ≈ 3 000 184 800 753,8964`, a
0,0017470 um do outro, `s = 0,0075`): `−1,91·10⁻⁶ ≤ λ ≤ −1,52·10⁻⁶`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −1,5261·10⁻⁶). -/
theorem par_mais_fragil_continuacao9 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300018480075389636015081554180 / 10 ^ 17| ≤ 252 / 10 ^ 20)
    (h₂ : |γ₂ - 300018480075389810718008697635 / 10 ^ 17| ≤ 310 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(191 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(152 : ℝ) / 100000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 174702 / 100000000) (hi := 174703 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-! ### Décima e décima primeira extensões: faixas 0–5 e 6–11 do C0 3 000 184 822 471,5

Runs 41889064559 (faixas 0–5) e 41889069781 (faixas 6–11), pastas `de_3000184822471.5/faixas_0-5/` e `faixas_6-11/`;
colagem das 12 faixas em `de_3000184822471.5/juntas_0-11/`: as 12 colagens conferem (a faixa 0 recalcula
`N(3 000 184 822 471,5) = 12 363 194 052 604`, o fim da nona extensão), déficit 0 em todas,
`3 000 184 822 471,5 < Im s ≤ 3 000 186 262 471,5` com 6 163 150 zeros, todos na reta (maior raio 5,01·10⁻¹⁸).
Faixas 0–5: `N` de 12 363 194 052 604 a 12 363 197 134 179 (3 081 575 zeros). Faixas 6–11: `N` de 12 363 197 134 179 a
12 363 200 215 754 (3 081 575 zeros). Hipóteses nomeadas `JanelaContinuacao2026j` e `JanelaContinuacao2026k`. -/

/-- **Janela da décima extensão (fora do kernel)**: todos os zeros com `3 000 184 822 471 < Im s ≤ 3 000 185 542 471`
estão na reta. -/
def JanelaContinuacao2026j : Prop := JanelaNaReta 3000184822471 3000185542471

/-- **Janela da décima primeira extensão (fora do kernel)**: todos os zeros com
`3 000 185 542 471 < Im s ≤ 3 000 186 262 471` estão na reta. -/
def JanelaContinuacao2026k : Prop := JanelaNaReta 3000185542471 3000186262471

/-- RH até `3 000 185 542 471`, condicional a Platt–Trudgian e às onze janelas da Arb. -/
theorem rhAteZ_continuacao10 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026)
    (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d)
    (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g)
    (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) :
    RHateZ 3000185542471 :=
  rhateZ_estende (rhAteZ_continuacao9 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9) (by exact_mod_cast hC10)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 185 542 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao10 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026)
    (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c)
    (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f)
    (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i)
    (hC10 : JanelaContinuacao2026j) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000185542471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima (rhAteZ_continuacao10 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10) h
  simpa using this

/-- **O par mais frágil das faixas 0–5** (zeros 12 363 196 174 310 e …311, `γ ≈ 3 000 185 318 201,2790`, a
0,0014072 um do outro, `s = 0,0060`): `−1,24·10⁻⁶ ≤ λ ≤ −9,90·10⁻⁷`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −9,9008·10⁻⁷). -/
theorem par_mais_fragil_continuacao10 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300018531820127897593825428491 / 10 ^ 17| ≤ 225 / 10 ^ 20)
    (h₂ : |γ₂ - 300018531820128038310647671951 / 10 ^ 17| ≤ 442 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(124 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(990 : ℝ) / 1000000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 140716 / 100000000) (hi := 140717 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-- RH até `3 000 186 262 471`, condicional a Platt–Trudgian e às doze janelas da Arb. -/
theorem rhAteZ_continuacao11 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026)
    (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d)
    (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g)
    (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j)
    (hC11 : JanelaContinuacao2026k) : RHateZ 3000186262471 :=
  rhateZ_estende (rhAteZ_continuacao10 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10) (by exact_mod_cast hC11)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 186 262 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao11 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026)
    (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c)
    (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f)
    (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i)
    (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000186262471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima (rhAteZ_continuacao11 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11) h
  simpa using this

/-- **O par mais frágil das faixas 6–11** (zeros 12 363 199 737 223 e …224, `γ ≈ 3 000 186 150 664,0726`, a
0,00071404 um do outro, `s = 0,0031`): `−3,19·10⁻⁷ ≤ λ ≤ −2,54·10⁻⁷`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −2,5493·10⁻⁷). -/
theorem par_mais_fragil_continuacao11 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300018615066407255234204360078 / 10 ^ 17| ≤ 161 / 10 ^ 20)
    (h₂ : |γ₂ - 300018615066407326638234569659 / 10 ^ 17| ≤ 391 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(319 : ℝ) / 1000000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(254 : ℝ) / 1000000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 71404 / 100000000) (hi := 71405 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

end ClayRiemannProof.Continuacao
