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

/-! ### Décima segunda e décima terceira extensões: faixas 0–5 e 6–11 do C0 3 000 186 262 471,5

Runs 41928307909 (faixas 0–5) e 41928311888 (faixas 6–11), pastas `de_3000186262471.5/faixas_0-5/` e `faixas_6-11/`;
colagem das 12 faixas em `de_3000186262471.5/juntas_0-11/`: as 12 colagens conferem (a faixa 0 recalcula
`N(3 000 186 262 471,5) = 12 363 200 215 754`, o fim da décima primeira extensão), déficit 0 em todas,
`3 000 186 262 471,5 < Im s ≤ 3 000 187 702 471,5` com 6 163 152 zeros, todos na reta (maior raio 5,01·10⁻¹⁸).
Faixas 0–5: `N` de 12 363 200 215 754 a 12 363 203 297 331 (3 081 577 zeros). Faixas 6–11: `N` de 12 363 203 297 331 a
12 363 206 378 906 (3 081 575 zeros). Hipóteses nomeadas `JanelaContinuacao2026l` e `JanelaContinuacao2026m`. -/

/-- **Janela da décima segunda extensão (fora do kernel)**: todos os zeros com
`3 000 186 262 471 < Im s ≤ 3 000 186 982 471` estão na reta. -/
def JanelaContinuacao2026l : Prop := JanelaNaReta 3000186262471 3000186982471

/-- **Janela da décima terceira extensão (fora do kernel)**: todos os zeros com
`3 000 186 982 471 < Im s ≤ 3 000 187 702 471` estão na reta. -/
def JanelaContinuacao2026m : Prop := JanelaNaReta 3000186982471 3000187702471

/-- RH até `3 000 186 982 471`, condicional a Platt–Trudgian e às treze janelas da Arb. -/
theorem rhAteZ_continuacao12 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026)
    (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d)
    (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g)
    (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j)
    (hC11 : JanelaContinuacao2026k) (hC12 : JanelaContinuacao2026l) : RHateZ 3000186982471 :=
  rhateZ_estende (rhAteZ_continuacao11 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11)
    (by exact_mod_cast hC12)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 186 982 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao12 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026)
    (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c)
    (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f)
    (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i)
    (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k) (hC12 : JanelaContinuacao2026l)
    (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000186982471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima
    (rhAteZ_continuacao12 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12) h
  simpa using this

/-- **O par mais frágil das faixas 0–5** (zeros 12 363 202 900 336 e …337, `γ ≈ 3 000 186 889 715,1992`, a
0,00108367 um do outro, `s = 0,0046`): `−7,34·10⁻⁷ ≤ λ ≤ −5,87·10⁻⁷`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −5,8718·10⁻⁷). -/
theorem par_mais_fragil_continuacao12 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300018688971519923945008925565 / 10 ^ 17| ≤ 162 / 10 ^ 20)
    (h₂ : |γ₂ - 300018688971520032312054629171 / 10 ^ 17| ≤ 209 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(734 : ℝ) / 1000000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(587 : ℝ) / 1000000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 108367 / 100000000) (hi := 108368 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-- RH até `3 000 187 702 471`, condicional a Platt–Trudgian e às catorze janelas da Arb. -/
theorem rhAteZ_continuacao13 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026)
    (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d)
    (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g)
    (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j)
    (hC11 : JanelaContinuacao2026k) (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) :
    RHateZ 3000187702471 :=
  rhateZ_estende (rhAteZ_continuacao12 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12)
    (by exact_mod_cast hC13)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 187 702 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao13 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026)
    (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c)
    (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f)
    (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i)
    (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k) (hC12 : JanelaContinuacao2026l)
    (hC13 : JanelaContinuacao2026m) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000187702471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima
    (rhAteZ_continuacao13 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13) h
  simpa using this

/-- **O par mais frágil das faixas 6–11** (zeros 12 363 204 425 878 e …879, `γ ≈ 3 000 187 246 153,1154`, a
0,00169501 um do outro, `s = 0,0073`): `−1,80·10⁻⁶ ≤ λ ≤ −1,43·10⁻⁶`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −1,4366·10⁻⁶). -/
theorem par_mais_fragil_continuacao13 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300018724615311535227778957587 / 10 ^ 17| ≤ 325 / 10 ^ 20)
    (h₂ : |γ₂ - 300018724615311704728892880888 / 10 ^ 17| ≤ 237 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(180 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(143 : ℝ) / 100000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 169501 / 100000000) (hi := 169502 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-! ### Décima quarta e décima quinta extensões: faixas 0–5 e 6–11 do C0 3 000 187 702 471,5

Runs 41993718376 (faixas 0–5) e 41993732554 (faixas 6–11), pastas `de_3000187702471.5/faixas_0-5/` e `faixas_6-11/`;
colagem das 12 faixas em `de_3000187702471.5/juntas_0-11/`: as 12 colagens conferem (a faixa 0 recalcula
`N(3 000 187 702 471,5) = 12 363 206 378 906`, o fim da décima terceira extensão), déficit 0 em todas,
`3 000 187 702 471,5 < Im s ≤ 3 000 189 142 471,5` com 6 163 149 zeros, todos na reta (maior raio 5,01·10⁻¹⁸).
Faixas 0–5: `N` de 12 363 206 378 906 a 12 363 209 460 481 (3 081 575 zeros). Faixas 6–11: `N` de 12 363 209 460 481 a
12 363 212 542 055 (3 081 574 zeros). Hipóteses nomeadas `JanelaContinuacao2026n` e `JanelaContinuacao2026o`. -/

/-- **Janela da décima quarta extensão (fora do kernel)**: todos os zeros com
`3 000 187 702 471 < Im s ≤ 3 000 188 422 471` estão na reta. -/
def JanelaContinuacao2026n : Prop := JanelaNaReta 3000187702471 3000188422471

/-- **Janela da décima quinta extensão (fora do kernel)**: todos os zeros com
`3 000 188 422 471 < Im s ≤ 3 000 189 142 471` estão na reta. -/
def JanelaContinuacao2026o : Prop := JanelaNaReta 3000188422471 3000189142471

/-- RH até `3 000 188 422 471`, condicional a Platt–Trudgian e às quinze janelas da Arb. -/
theorem rhAteZ_continuacao14 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026)
    (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d)
    (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g)
    (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j)
    (hC11 : JanelaContinuacao2026k) (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m)
    (hC14 : JanelaContinuacao2026n) : RHateZ 3000188422471 :=
  rhateZ_estende (rhAteZ_continuacao13 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13)
    (by exact_mod_cast hC14)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 188 422 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao14 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026)
    (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c)
    (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f)
    (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i)
    (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k) (hC12 : JanelaContinuacao2026l)
    (hC13 : JanelaContinuacao2026m)
    (hC14 : JanelaContinuacao2026n) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000188422471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima
    (rhAteZ_continuacao14 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14) h
  simpa using this

/-- **O par mais frágil das faixas 0–5** (zeros 12 363 208 353 330 e …331, `γ ≈ 3 000 188 163 789,4398`, a
0,00149485 um do outro, `s = 0,0064`): `−1,40·10⁻⁶ ≤ λ ≤ −1,11·10⁻⁶`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −1,1173·10⁻⁶). -/
theorem par_mais_fragil_continuacao14 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300018816378943976313977878318 / 10 ^ 17| ≤ 342 / 10 ^ 20)
    (h₂ : |γ₂ - 300018816378944125799639233284 / 10 ^ 17| ≤ 225 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(140 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(111 : ℝ) / 100000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 149485 / 100000000) (hi := 149486 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-- RH até `3 000 189 142 471`, condicional a Platt–Trudgian e às dezesseis janelas da Arb. -/
theorem rhAteZ_continuacao15 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026)
    (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d)
    (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g)
    (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j)
    (hC11 : JanelaContinuacao2026k) (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m)
    (hC14 : JanelaContinuacao2026n) (hC15 : JanelaContinuacao2026o) : RHateZ 3000189142471 :=
  rhateZ_estende (rhAteZ_continuacao14 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14)
    (by exact_mod_cast hC15)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 189 142 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao15 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026)
    (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c)
    (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f)
    (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i)
    (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k) (hC12 : JanelaContinuacao2026l)
    (hC13 : JanelaContinuacao2026m)
    (hC14 : JanelaContinuacao2026n) (hC15 : JanelaContinuacao2026o) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000189142471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima
    (rhAteZ_continuacao15 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15) h
  simpa using this

/-- **O par mais frágil das faixas 6–11** (zeros 12 363 211 536 708 e …709, `γ ≈ 3 000 188 907 575,2365`, a
0,00191926 um do outro, `s = 0,0082`): `−2,31·10⁻⁶ ≤ λ ≤ −1,84·10⁻⁶`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −1,8419·10⁻⁶). -/
theorem par_mais_fragil_continuacao15 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300018890757523652252505943683 / 10 ^ 17| ≤ 451 / 10 ^ 20)
    (h₂ : |γ₂ - 300018890757523844179311411900 / 10 ^ 17| ≤ 160 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(231 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(184 : ℝ) / 100000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 191926 / 100000000) (hi := 191927 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-! ### Décima sexta e décima sétima extensões: faixas 0–5 e 6–11 do C0 3 000 189 142 471,5

Runs 42032164321 (faixas 0–5) e 42032176191 (faixas 6–11), pastas `de_3000189142471.5/faixas_0-5/` e `faixas_6-11/`;
colagem das 12 faixas em `de_3000189142471.5/juntas_0-11/`: as 12 colagens conferem (a faixa 0 recalcula
`N(3 000 189 142 471,5) = 12 363 212 542 055`, o fim da décima quinta extensão), déficit 0 em todas,
`3 000 189 142 471,5 < Im s ≤ 3 000 190 582 471,5` com 6 163 152 zeros, todos na reta (maior raio 5,01·10⁻¹⁸).
Faixas 0–5: `N` de 12 363 212 542 055 a 12 363 215 623 632 (3 081 577 zeros). Faixas 6–11: `N` de 12 363 215 623 632 a
12 363 218 705 207 (3 081 575 zeros). Hipóteses nomeadas `JanelaContinuacao2026p` e `JanelaContinuacao2026q`. -/

/-- **Janela da décima sexta extensão (fora do kernel)**: todos os zeros com
`3 000 189 142 471 < Im s ≤ 3 000 189 862 471` estão na reta. -/
def JanelaContinuacao2026p : Prop := JanelaNaReta 3000189142471 3000189862471

/-- **Janela da décima sétima extensão (fora do kernel)**: todos os zeros com
`3 000 189 862 471 < Im s ≤ 3 000 190 582 471` estão na reta. -/
def JanelaContinuacao2026q : Prop := JanelaNaReta 3000189862471 3000190582471

/-- RH até `3 000 189 862 471`, condicional a Platt–Trudgian e às dezessete janelas da Arb. -/
theorem rhAteZ_continuacao16 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026)
    (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d)
    (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g)
    (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j)
    (hC11 : JanelaContinuacao2026k) (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m)
    (hC14 : JanelaContinuacao2026n) (hC15 : JanelaContinuacao2026o)
    (hC16 : JanelaContinuacao2026p) : RHateZ 3000189862471 :=
  rhateZ_estende (rhAteZ_continuacao15 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15)
    (by exact_mod_cast hC16)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 189 862 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao16 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026)
    (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c)
    (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f)
    (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i)
    (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k) (hC12 : JanelaContinuacao2026l)
    (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n) (hC15 : JanelaContinuacao2026o)
    (hC16 : JanelaContinuacao2026p) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000189862471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima
    (rhAteZ_continuacao16 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16) h
  simpa using this

/-- **O par mais frágil das faixas 0–5** (zeros 12 363 213 419 057 e …058, `γ ≈ 3 000 189 347 379,8704`, a
0,00163686 um do outro, `s = 0,0070`): `−1,68·10⁻⁶ ≤ λ ≤ −1,33·10⁻⁶`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −1,3397·10⁻⁶). -/
theorem par_mais_fragil_continuacao16 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300018934737987038291894795048 / 10 ^ 17| ≤ 398 / 10 ^ 20)
    (h₂ : |γ₂ - 300018934737987201978609873470 / 10 ^ 17| ≤ 317 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(168 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(133 : ℝ) / 100000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 163686 / 100000000) (hi := 163687 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-- RH até `3 000 190 582 471`, condicional a Platt–Trudgian e às dezoito janelas da Arb. -/
theorem rhAteZ_continuacao17 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026)
    (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d)
    (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g)
    (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j)
    (hC11 : JanelaContinuacao2026k) (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m)
    (hC14 : JanelaContinuacao2026n) (hC15 : JanelaContinuacao2026o)
    (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q) : RHateZ 3000190582471 :=
  rhateZ_estende (rhAteZ_continuacao16 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16)
    (by exact_mod_cast hC17)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 190 582 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao17 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026)
    (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c)
    (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f)
    (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i)
    (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k) (hC12 : JanelaContinuacao2026l)
    (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n) (hC15 : JanelaContinuacao2026o)
    (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000190582471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima
    (rhAteZ_continuacao17 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17) h
  simpa using this

/-- **O par mais frágil das faixas 6–11** (zeros 12 363 216 568 001 e …002, `γ ≈ 3 000 190 083 120,2069`, a
0,00187760 um do outro, `s = 0,0080`): `−2,21·10⁻⁶ ≤ λ ≤ −1,76·10⁻⁶`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −1,7628·10⁻⁶). -/
theorem par_mais_fragil_continuacao17 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300019008312020688904652937996 / 10 ^ 17| ≤ 495 / 10 ^ 20)
    (h₂ : |γ₂ - 300019008312020876665589667226 / 10 ^ 17| ≤ 404 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(221 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(176 : ℝ) / 100000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 187760 / 100000000) (hi := 187761 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-! ### Décima oitava e décima nona extensões: faixas 0–5 e 6–11 do C0 3 000 190 582 471,5

Runs 42080945931 (faixas 0–5) e 42080958292 (faixas 6–11), pastas `de_3000190582471.5/faixas_0-5/` e `faixas_6-11/`;
colagem das 12 faixas em `de_3000190582471.5/juntas_0-11/`: as 12 colagens conferem (a faixa 0 recalcula
`N(3 000 190 582 471,5) = 12 363 218 705 207`, o fim da décima sétima extensão), déficit 0 em todas,
`3 000 190 582 471,5 < Im s ≤ 3 000 192 022 471,5` com 6 163 152 zeros, todos na reta (maior raio 5,01·10⁻¹⁸).
Faixas 0–5: `N` de 12 363 218 705 207 a 12 363 221 786 783 (3 081 576 zeros). Faixas 6–11: `N` de 12 363 221 786 783 a
12 363 224 868 359 (3 081 576 zeros). Hipóteses nomeadas `JanelaContinuacao2026r` e `JanelaContinuacao2026s`. -/

/-- **Janela da décima oitava extensão (fora do kernel)**: todos os zeros com
`3 000 190 582 471 < Im s ≤ 3 000 191 302 471` estão na reta. -/
def JanelaContinuacao2026r : Prop := JanelaNaReta 3000190582471 3000191302471

/-- **Janela da décima nona extensão (fora do kernel)**: todos os zeros com
`3 000 191 302 471 < Im s ≤ 3 000 192 022 471` estão na reta. -/
def JanelaContinuacao2026s : Prop := JanelaNaReta 3000191302471 3000192022471

/-- RH até `3 000 191 302 471`, condicional a Platt–Trudgian e às dezenove janelas da Arb. -/
theorem rhAteZ_continuacao18 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026)
    (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d)
    (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g)
    (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j)
    (hC11 : JanelaContinuacao2026k) (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m)
    (hC14 : JanelaContinuacao2026n) (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p)
    (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) : RHateZ 3000191302471 :=
  rhateZ_estende (rhAteZ_continuacao17 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17)
    (by exact_mod_cast hC18)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 191 302 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao18 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026)
    (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c)
    (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f)
    (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i)
    (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k) (hC12 : JanelaContinuacao2026l)
    (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n) (hC15 : JanelaContinuacao2026o)
    (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000191302471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima
    (rhAteZ_continuacao18 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18) h
  simpa using this

/-- **O par mais frágil das faixas 0–5** (zeros 12 363 221 560 334 e …335, `γ ≈ 3 000 191 249 562,4347`, a
0,00148440 um do outro, `s = 0,0064`): `−1,38·10⁻⁶ ≤ λ ≤ −1,10·10⁻⁶`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −1,1018·10⁻⁶). -/
theorem par_mais_fragil_continuacao18 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300019124956243466307864732155 / 10 ^ 17| ≤ 393 / 10 ^ 20)
    (h₂ : |γ₂ - 300019124956243614748645571793 / 10 ^ 17| ≤ 248 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(138 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(110 : ℝ) / 100000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 148440 / 100000000) (hi := 148441 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-- RH até `3 000 192 022 471`, condicional a Platt–Trudgian e às vinte janelas da Arb. -/
theorem rhAteZ_continuacao19 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026)
    (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d)
    (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g)
    (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j)
    (hC11 : JanelaContinuacao2026k) (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m)
    (hC14 : JanelaContinuacao2026n) (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p)
    (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) : RHateZ 3000192022471 :=
  rhateZ_estende (rhAteZ_continuacao18 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18)
    (by exact_mod_cast hC19)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 192 022 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao19 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026)
    (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c)
    (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f)
    (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i)
    (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k) (hC12 : JanelaContinuacao2026l)
    (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n) (hC15 : JanelaContinuacao2026o)
    (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000192022471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima
    (rhAteZ_continuacao19 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19) h
  simpa using this

/-- **O par mais frágil das faixas 6–11** (zeros 12 363 224 051 931 e …932, `γ ≈ 3 000 191 831 715,8820`, a
0,00127684 um do outro, `s = 0,0055`): `−1,02·10⁻⁶ ≤ λ ≤ −8,15·10⁻⁷`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −8,152·10⁻⁷; o segundo raio, 4,99·10⁻¹⁹, vai arredondado para cima, 5,0·10⁻¹⁹). -/
theorem par_mais_fragil_continuacao19 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300019183171588203123583330509 / 10 ^ 17| ≤ 409 / 10 ^ 20)
    (h₂ : |γ₂ - 300019183171588330807735452128 / 10 ^ 17| ≤ 50 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(102 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(815 : ℝ) / 1000000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 127684 / 100000000) (hi := 127685 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-! ### Vigésima e vigésima primeira extensões: faixas 0–5 e 6–11 do C0 3 000 192 022 471,5

Runs 42122478758 (faixas 0–5) e 42122490265 (faixas 6–11), pastas `de_3000192022471.5/faixas_0-5/` e `faixas_6-11/`;
colagem das 12 faixas em `de_3000192022471.5/juntas_0-11/`: as 12 colagens conferem (a faixa 0 recalcula
`N(3 000 192 022 471,5) = 12 363 224 868 359`, o fim da décima nona extensão), déficit 0 em todas,
`3 000 192 022 471,5 < Im s ≤ 3 000 193 462 471,5` com 6 163 151 zeros, todos na reta (maior raio 5,01·10⁻¹⁸).
Faixas 0–5: `N` de 12 363 224 868 359 a 12 363 227 949 934 (3 081 575 zeros). Faixas 6–11: `N` de 12 363 227 949 934 a
12 363 231 031 510 (3 081 576 zeros). Hipóteses nomeadas `JanelaContinuacao2026t` e `JanelaContinuacao2026u`. -/

/-- **Janela da vigésima extensão (fora do kernel)**: todos os zeros com
`3 000 192 022 471 < Im s ≤ 3 000 192 742 471` estão na reta. -/
def JanelaContinuacao2026t : Prop := JanelaNaReta 3000192022471 3000192742471

/-- **Janela da vigésima primeira extensão (fora do kernel)**: todos os zeros com
`3 000 192 742 471 < Im s ≤ 3 000 193 462 471` estão na reta. -/
def JanelaContinuacao2026u : Prop := JanelaNaReta 3000192742471 3000193462471

/-- RH até `3 000 192 742 471`, condicional a Platt–Trudgian e às vinte e uma janelas da Arb. -/
theorem rhAteZ_continuacao20 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026)
    (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d)
    (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g)
    (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j)
    (hC11 : JanelaContinuacao2026k) (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m)
    (hC14 : JanelaContinuacao2026n) (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p)
    (hC17 : JanelaContinuacao2026q) (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s)
    (hC20 : JanelaContinuacao2026t) : RHateZ 3000192742471 :=
  rhateZ_estende (rhAteZ_continuacao19 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19)
    (by exact_mod_cast hC20)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 192 742 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao20 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026)
    (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c)
    (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f)
    (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i)
    (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k) (hC12 : JanelaContinuacao2026l)
    (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n) (hC15 : JanelaContinuacao2026o)
    (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q) (hC18 : JanelaContinuacao2026r)
    (hC19 : JanelaContinuacao2026s)
    (hC20 : JanelaContinuacao2026t) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000192742471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima
    (rhAteZ_continuacao20 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20) h
  simpa using this

/-- **O par mais frágil das faixas 0–5** (zeros 12 363 226 933 478 e …479, `γ ≈ 3 000 192 504 979,8151`, a
0,00168622 um do outro, `s = 0,0072`): `−1,78·10⁻⁶ ≤ λ ≤ −1,42·10⁻⁶`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −1,4217·10⁻⁶; o primeiro raio, 3,72·10⁻¹⁹, vai arredondado para cima, 3,8·10⁻¹⁹). -/
theorem par_mais_fragil_continuacao20 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300019250497981508072414200062 / 10 ^ 17| ≤ 38 / 10 ^ 20)
    (h₂ : |γ₂ - 300019250497981676695005020570 / 10 ^ 17| ≤ 367 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(178 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(142 : ℝ) / 100000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 168622 / 100000000) (hi := 168623 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-- RH até `3 000 193 462 471`, condicional a Platt–Trudgian e às vinte e duas janelas da Arb. -/
theorem rhAteZ_continuacao21 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026)
    (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d)
    (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g)
    (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j)
    (hC11 : JanelaContinuacao2026k) (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m)
    (hC14 : JanelaContinuacao2026n) (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p)
    (hC17 : JanelaContinuacao2026q) (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s)
    (hC20 : JanelaContinuacao2026t) (hC21 : JanelaContinuacao2026u) : RHateZ 3000193462471 :=
  rhateZ_estende (rhAteZ_continuacao20 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20)
    (by exact_mod_cast hC21)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 193 462 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao21 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026)
    (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b) (hC3 : JanelaContinuacao2026c)
    (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e) (hC6 : JanelaContinuacao2026f)
    (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h) (hC9 : JanelaContinuacao2026i)
    (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k) (hC12 : JanelaContinuacao2026l)
    (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n) (hC15 : JanelaContinuacao2026o)
    (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q) (hC18 : JanelaContinuacao2026r)
    (hC19 : JanelaContinuacao2026s)
    (hC20 : JanelaContinuacao2026t) (hC21 : JanelaContinuacao2026u) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000193462471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima
    (rhAteZ_continuacao21 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21) h
  simpa using this

/-- **O par mais frágil das faixas 6–11** (zeros 12 363 229 260 166 e …167, `γ ≈ 3 000 193 048 602,9184`, a
0,00103727 um do outro, `s = 0,0044`): `−6,73·10⁻⁷ ≤ λ ≤ −5,37·10⁻⁷`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −5,380·10⁻⁷). -/
theorem par_mais_fragil_continuacao21 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300019304860291842976421189866 / 10 ^ 17| ≤ 157 / 10 ^ 20)
    (h₂ : |γ₂ - 300019304860291946704150900879 / 10 ^ 17| ≤ 450 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(673 : ℝ) / 1000000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(537 : ℝ) / 1000000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 103727 / 100000000) (hi := 103728 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-! ### Vigésima segunda e vigésima terceira extensões: faixas 0–5 e 6–11 do C0 3 000 193 462 471,5

Runs 42698687986 (faixas 0–5) e 42698701000 (faixas 6–11), pastas `de_3000193462471.5/faixas_0-5/` e `faixas_6-11/`;
colagem das 12 faixas em `de_3000193462471.5/juntas_0-11/`: as 12 colagens conferem (a faixa 0 recalcula
`N(3 000 193 462 471,5) = 12 363 231 031 510`, o fim da vigésima primeira extensão), déficit 0 em todas,
`3 000 193 462 471,5 < Im s ≤ 3 000 194 902 471,5` com 6 163 152 zeros, todos na reta (maior raio 5,01·10⁻¹⁸).
Faixas 0–5: `N` de 12 363 231 031 510 a 12 363 234 113 085 (3 081 575 zeros). Faixas 6–11: `N` de 12 363 234 113 085 a
12 363 237 194 662 (3 081 577 zeros). Hipóteses nomeadas `JanelaContinuacao2026v` e `JanelaContinuacao2026w`. -/

/-- **Janela da vigésima segunda extensão (fora do kernel)**: todos os zeros com
`3 000 193 462 471 < Im s ≤ 3 000 194 182 471` estão na reta. -/
def JanelaContinuacao2026v : Prop := JanelaNaReta 3000193462471 3000194182471

/-- **Janela da vigésima terceira extensão (fora do kernel)**: todos os zeros com
`3 000 194 182 471 < Im s ≤ 3 000 194 902 471` estão na reta. -/
def JanelaContinuacao2026w : Prop := JanelaNaReta 3000194182471 3000194902471

/-- RH até `3 000 194 182 471`, condicional a Platt–Trudgian e às janelas da Arb até a vigésima segunda extensão. -/
theorem rhAteZ_continuacao22 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u)
    (hC22 : JanelaContinuacao2026v) : RHateZ 3000194182471 :=
  rhateZ_estende (rhAteZ_continuacao21 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21)
    (by exact_mod_cast hC22)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 194 182 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao22 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u)
    (hC22 : JanelaContinuacao2026v) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000194182471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima
    (rhAteZ_continuacao22 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22) h
  simpa using this

/-- **O par mais frágil das faixas 0–5** (zeros 12 363 232 451 856 e …857, `γ ≈ 3 000 193 794 330,6765`, a
0,00111858 um do outro, `s = 0,0048`): `−7,83·10⁻⁷ ≤ λ ≤ −6,25·10⁻⁷`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −6,256·10⁻⁷). -/
theorem par_mais_fragil_continuacao22 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300019379433067648032791119270 / 10 ^ 17| ≤ 204 / 10 ^ 20)
    (h₂ : |γ₂ - 300019379433067759891760161083 / 10 ^ 17| ≤ 482 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(783 : ℝ) / 1000000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(625 : ℝ) / 1000000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 111858 / 100000000) (hi := 111859 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-- RH até `3 000 194 902 471`, condicional a Platt–Trudgian e às janelas da Arb até a vigésima terceira extensão. -/
theorem rhAteZ_continuacao23 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u)
    (hC22 : JanelaContinuacao2026v) (hC23 : JanelaContinuacao2026w) : RHateZ 3000194902471 :=
  rhateZ_estende (rhAteZ_continuacao22 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22)
    (by exact_mod_cast hC23)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 194 902 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao23 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u)
    (hC22 : JanelaContinuacao2026v) (hC23 : JanelaContinuacao2026w) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000194902471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima
    (rhAteZ_continuacao23 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22 hC23) h
  simpa using this

/-- **O par mais frágil das faixas 6–11** (zeros 12 363 236 283 824 e …825, `γ ≈ 3 000 194 689 657,3420`, a
0,00133214 um do outro, `s = 0,0057`): `−1,11·10⁻⁶ ≤ λ ≤ −8,87·10⁻⁷`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −8,873·10⁻⁷; o primeiro raio, 6,60·10⁻¹⁹, vai como 6,6·10⁻¹⁹). -/
theorem par_mais_fragil_continuacao23 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300019468965734197468845573440 / 10 ^ 17| ≤ 66 / 10 ^ 20)
    (h₂ : |γ₂ - 300019468965734330683200978287 / 10 ^ 17| ≤ 483 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(111 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(887 : ℝ) / 1000000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 133214 / 100000000) (hi := 133215 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-! ### Vigésima quarta e vigésima quinta extensões: faixas 0–5 e 6–11 do C0 3 000 194 902 471,5

Runs 42735880703 (faixas 0–5) e 42735893892 (faixas 6–11), pastas `de_3000194902471.5/faixas_0-5/` e `faixas_6-11/`;
colagem das 12 faixas em `de_3000194902471.5/juntas_0-11/`: as 12 colagens conferem (a faixa 0 recalcula
`N(3 000 194 902 471,5) = 12 363 237 194 662`, o fim da vigésima terceira extensão), déficit 0 em todas,
`3 000 194 902 471,5 < Im s ≤ 3 000 196 342 471,5` com 6 163 151 zeros, todos na reta (maior raio 5,01·10⁻¹⁸).
Faixas 0–5: `N` de 12 363 237 194 662 a 12 363 240 276 236 (3 081 574 zeros). Faixas 6–11: `N` de 12 363 240 276 236 a
12 363 243 357 813 (3 081 577 zeros). Hipóteses nomeadas `JanelaContinuacao2026x` e `JanelaContinuacao2026y`. -/

/-- **Janela da vigésima quarta extensão (fora do kernel)**: todos os zeros com
`3 000 194 902 471 < Im s ≤ 3 000 195 622 471` estão na reta. -/
def JanelaContinuacao2026x : Prop := JanelaNaReta 3000194902471 3000195622471

/-- **Janela da vigésima quinta extensão (fora do kernel)**: todos os zeros com
`3 000 195 622 471 < Im s ≤ 3 000 196 342 471` estão na reta. -/
def JanelaContinuacao2026y : Prop := JanelaNaReta 3000195622471 3000196342471

/-- RH até `3 000 195 622 471`, condicional a Platt–Trudgian e às janelas da Arb até a vigésima quarta extensão. -/
theorem rhAteZ_continuacao24 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u) (hC22 : JanelaContinuacao2026v) (hC23 : JanelaContinuacao2026w)
    (hC24 : JanelaContinuacao2026x) : RHateZ 3000195622471 :=
  rhateZ_estende (rhAteZ_continuacao23 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22 hC23)
    (by exact_mod_cast hC24)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 195 622 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao24 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u) (hC22 : JanelaContinuacao2026v) (hC23 : JanelaContinuacao2026w)
    (hC24 : JanelaContinuacao2026x) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000195622471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima
    (rhAteZ_continuacao24 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22 hC23 hC24) h
  simpa using this

/-- **O par mais frágil das faixas 0–5** (zeros 12 363 238 243 209 e …210, `γ ≈ 3 000 195 147 461,2204`, a
0,00110144 um do outro, `s = 0,0047`): `−7,59·10⁻⁷ ≤ λ ≤ −6,06·10⁻⁷`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −6,066·10⁻⁷). -/
theorem par_mais_fragil_continuacao24 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300019514746122040545414147661 / 10 ^ 17| ≤ 398 / 10 ^ 20)
    (h₂ : |γ₂ - 300019514746122150689796010598 / 10 ^ 17| ≤ 294 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(759 : ℝ) / 1000000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(606 : ℝ) / 1000000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 110144 / 100000000) (hi := 110145 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-- RH até `3 000 196 342 471`, condicional a Platt–Trudgian e às janelas da Arb até a vigésima quinta extensão. -/
theorem rhAteZ_continuacao25 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u) (hC22 : JanelaContinuacao2026v) (hC23 : JanelaContinuacao2026w)
    (hC24 : JanelaContinuacao2026x) (hC25 : JanelaContinuacao2026y) : RHateZ 3000196342471 :=
  rhateZ_estende (rhAteZ_continuacao24 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22 hC23 hC24)
    (by exact_mod_cast hC25)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 196 342 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao25 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u) (hC22 : JanelaContinuacao2026v) (hC23 : JanelaContinuacao2026w)
    (hC24 : JanelaContinuacao2026x) (hC25 : JanelaContinuacao2026y) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000196342471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima
    (rhAteZ_continuacao25 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22 hC23 hC24 hC25) h
  simpa using this

/-- **O par mais frágil das faixas 6–11** (zeros 12 363 243 053 855 e …856, `γ ≈ 3 000 196 271 452,6832`, a
0,00128093 um do outro, `s = 0,0055`): `−1,03·10⁻⁶ ≤ λ ≤ −8,20·10⁻⁷`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −8,204·10⁻⁷). -/
theorem par_mais_fragil_continuacao25 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300019627145268317853622927214 / 10 ^ 17| ≤ 483 / 10 ^ 20)
    (h₂ : |γ₂ - 300019627145268445946792220260 / 10 ^ 17| ≤ 296 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(103 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(820 : ℝ) / 1000000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 128093 / 100000000) (hi := 128094 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-! ### Vigésima sexta e vigésima sétima extensões: faixas 0–5 e 6–11 do C0 3 000 196 342 471,5

Runs 43020912910 (faixas 0–5) e 43020926543 (faixas 6–11), pastas `de_3000196342471.5/faixas_0-5/` e `faixas_6-11/`;
colagem das 12 faixas em `de_3000196342471.5/juntas_0-11/`: as 12 colagens conferem (a faixa 0 recalcula
`N(3 000 196 342 471,5) = 12 363 243 357 813`, o fim da vigésima quinta extensão), déficit 0 em todas,
`3 000 196 342 471,5 < Im s ≤ 3 000 197 782 471,5` com 6 163 151 zeros, todos na reta (maior raio 5,01·10⁻¹⁸).
Faixas 0–5: `N` de 12 363 243 357 813 a 12 363 246 439 389 (3 081 576 zeros). Faixas 6–11: `N` de 12 363 246 439 389 a
12 363 249 520 964 (3 081 575 zeros). Hipóteses nomeadas `JanelaContinuacao2026z` e `JanelaContinuacao2026aa`. -/

/-- **Janela da vigésima sexta extensão (fora do kernel)**: todos os zeros com
`3 000 196 342 471 < Im s ≤ 3 000 197 062 471` estão na reta. -/
def JanelaContinuacao2026z : Prop := JanelaNaReta 3000196342471 3000197062471

/-- **Janela da vigésima sétima extensão (fora do kernel)**: todos os zeros com
`3 000 197 062 471 < Im s ≤ 3 000 197 782 471` estão na reta. -/
def JanelaContinuacao2026aa : Prop := JanelaNaReta 3000197062471 3000197782471

/-- RH até `3 000 197 062 471`, condicional a Platt–Trudgian e às janelas da Arb até a vigésima sexta extensão. -/
theorem rhAteZ_continuacao26 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u) (hC22 : JanelaContinuacao2026v) (hC23 : JanelaContinuacao2026w)
    (hC24 : JanelaContinuacao2026x) (hC25 : JanelaContinuacao2026y)
    (hC26 : JanelaContinuacao2026z) : RHateZ 3000197062471 :=
  rhateZ_estende (rhAteZ_continuacao25 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22 hC23 hC24 hC25)
    (by exact_mod_cast hC26)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 197 062 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao26 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u) (hC22 : JanelaContinuacao2026v) (hC23 : JanelaContinuacao2026w)
    (hC24 : JanelaContinuacao2026x) (hC25 : JanelaContinuacao2026y)
    (hC26 : JanelaContinuacao2026z) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000197062471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima
    (rhAteZ_continuacao26 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22 hC23 hC24 hC25 hC26) h
  simpa using this

/-- **O par mais frágil das faixas 0–5** (zeros 12 363 245 848 726 e …727, `γ ≈ 3 000 196 924 465,0867`, a
0,00259150 um do outro, `s = 0,0111`): `−4,20·10⁻⁶ ≤ λ ≤ −3,35·10⁻⁶`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −3,358·10⁻⁶). -/
theorem par_mais_fragil_continuacao26 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300019692446508670077269566213 / 10 ^ 17| ≤ 175 / 10 ^ 20)
    (h₂ : |γ₂ - 300019692446508929228249508320 / 10 ^ 17| ≤ 360 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(420 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(335 : ℝ) / 100000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 259150 / 100000000) (hi := 259151 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-- RH até `3 000 197 782 471`, condicional a Platt–Trudgian e às janelas da Arb até a vigésima sétima extensão. -/
theorem rhAteZ_continuacao27 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u) (hC22 : JanelaContinuacao2026v) (hC23 : JanelaContinuacao2026w)
    (hC24 : JanelaContinuacao2026x) (hC25 : JanelaContinuacao2026y)
    (hC26 : JanelaContinuacao2026z) (hC27 : JanelaContinuacao2026aa) : RHateZ 3000197782471 :=
  rhateZ_estende (rhAteZ_continuacao26 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22 hC23 hC24 hC25 hC26)
    (by exact_mod_cast hC27)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 197 782 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao27 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u) (hC22 : JanelaContinuacao2026v) (hC23 : JanelaContinuacao2026w)
    (hC24 : JanelaContinuacao2026x) (hC25 : JanelaContinuacao2026y)
    (hC26 : JanelaContinuacao2026z) (hC27 : JanelaContinuacao2026aa) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000197782471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima
    (rhAteZ_continuacao27 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22 hC23 hC24 hC25 hC26 hC27) h
  simpa using this

/-- **O par mais frágil das faixas 6–11** (zeros 12 363 246 600 389 e …390, `γ ≈ 3 000 197 100 088,7312`, a
0,00118310 um do outro, `s = 0,0051`): `−8,75·10⁻⁷ ≤ λ ≤ −6,99·10⁻⁷`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −6,999·10⁻⁷). -/
theorem par_mais_fragil_continuacao27 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300019710008873115315602225012 / 10 ^ 17| ≤ 430 / 10 ^ 20)
    (h₂ : |γ₂ - 300019710008873233626542980171 / 10 ^ 17| ≤ 271 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(875 : ℝ) / 1000000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(699 : ℝ) / 1000000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 118310 / 100000000) (hi := 118311 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-! ### Vigésima oitava e vigésima nona extensões: faixas 0–5 e 6–11 do C0 3 000 197 782 471,5

Runs 43098888149 (faixas 0–5) e 43098890915 (faixas 6–11), pastas `de_3000197782471.5/faixas_0-5/` e `faixas_6-11/`;
colagem das 12 faixas em `de_3000197782471.5/juntas_0-11/`: as 12 colagens conferem (a faixa 0 recalcula
`N(3 000 197 782 471,5) = 12 363 249 520 964`, o fim da vigésima sétima extensão), déficit 0 em todas,
`3 000 197 782 471,5 < Im s ≤ 3 000 199 222 471,5` com 6 163 153 zeros, todos na reta (maior raio 5,01·10⁻¹⁸).
Faixas 0–5: `N` de 12 363 249 520 964 a 12 363 252 602 540 (3 081 576 zeros). Faixas 6–11: `N` de 12 363 252 602 540 a
12 363 255 684 117 (3 081 577 zeros). Hipóteses nomeadas `JanelaContinuacao2026ab` e `JanelaContinuacao2026ac`. -/

/-- **Janela da vigésima oitava extensão (fora do kernel)**: todos os zeros com
`3 000 197 782 471 < Im s ≤ 3 000 198 502 471` estão na reta. -/
def JanelaContinuacao2026ab : Prop := JanelaNaReta 3000197782471 3000198502471

/-- **Janela da vigésima nona extensão (fora do kernel)**: todos os zeros com
`3 000 198 502 471 < Im s ≤ 3 000 199 222 471` estão na reta. -/
def JanelaContinuacao2026ac : Prop := JanelaNaReta 3000198502471 3000199222471

/-- RH até `3 000 198 502 471`, condicional a Platt–Trudgian e às janelas da Arb até a vigésima oitava extensão. -/
theorem rhAteZ_continuacao28 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u) (hC22 : JanelaContinuacao2026v) (hC23 : JanelaContinuacao2026w)
    (hC24 : JanelaContinuacao2026x) (hC25 : JanelaContinuacao2026y) (hC26 : JanelaContinuacao2026z)
    (hC27 : JanelaContinuacao2026aa)
    (hC28 : JanelaContinuacao2026ab) : RHateZ 3000198502471 :=
  rhateZ_estende (rhAteZ_continuacao27 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22 hC23 hC24 hC25 hC26 hC27)
    (by exact_mod_cast hC28)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 198 502 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao28 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u) (hC22 : JanelaContinuacao2026v) (hC23 : JanelaContinuacao2026w)
    (hC24 : JanelaContinuacao2026x) (hC25 : JanelaContinuacao2026y) (hC26 : JanelaContinuacao2026z)
    (hC27 : JanelaContinuacao2026aa)
    (hC28 : JanelaContinuacao2026ab) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000198502471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima
    (rhAteZ_continuacao28 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22 hC23 hC24 hC25 hC26 hC27 hC28) h
  simpa using this

/-- **O par mais frágil das faixas 0–5** (zeros 12 363 251 751 829 e …830, `γ ≈ 3 000 198 303 705,7252`, a
0,00158708 um do outro, `s = 0,0068`): `−1,58·10⁻⁶ ≤ λ ≤ −1,25·10⁻⁶`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −1,259·10⁻⁶). -/
theorem par_mais_fragil_continuacao28 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300019830370572516668994552339 / 10 ^ 17| ≤ 421 / 10 ^ 20)
    (h₂ : |γ₂ - 300019830370572675377792978751 / 10 ^ 17| ≤ 143 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(158 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(125 : ℝ) / 100000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 158708 / 100000000) (hi := 158709 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-- RH até `3 000 199 222 471`, condicional a Platt–Trudgian e às janelas da Arb até a vigésima nona extensão. -/
theorem rhAteZ_continuacao29 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u) (hC22 : JanelaContinuacao2026v) (hC23 : JanelaContinuacao2026w)
    (hC24 : JanelaContinuacao2026x) (hC25 : JanelaContinuacao2026y) (hC26 : JanelaContinuacao2026z)
    (hC27 : JanelaContinuacao2026aa)
    (hC28 : JanelaContinuacao2026ab) (hC29 : JanelaContinuacao2026ac) : RHateZ 3000199222471 :=
  rhateZ_estende (rhAteZ_continuacao28 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22 hC23 hC24 hC25 hC26 hC27 hC28)
    (by exact_mod_cast hC29)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 199 222 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao29 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u) (hC22 : JanelaContinuacao2026v) (hC23 : JanelaContinuacao2026w)
    (hC24 : JanelaContinuacao2026x) (hC25 : JanelaContinuacao2026y) (hC26 : JanelaContinuacao2026z)
    (hC27 : JanelaContinuacao2026aa)
    (hC28 : JanelaContinuacao2026ab) (hC29 : JanelaContinuacao2026ac) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000199222471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima
    (rhAteZ_continuacao29 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22 hC23 hC24 hC25 hC26 hC27 hC28 hC29) h
  simpa using this

/-- **O par mais frágil das faixas 6–11** (zeros 12 363 254 630 577 e …578, `γ ≈ 3 000 198 976 315,6366`, a
0,00155331 um do outro, `s = 0,0066`): `−1,51·10⁻⁶ ≤ λ ≤ −1,20·10⁻⁶`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −1,206·10⁻⁶). -/
theorem par_mais_fragil_continuacao29 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300019897631563658113618279041 / 10 ^ 17| ≤ 393 / 10 ^ 20)
    (h₂ : |γ₂ - 300019897631563813445224234056 / 10 ^ 17| ≤ 90 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(151 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(120 : ℝ) / 100000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 155331 / 100000000) (hi := 155332 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-! ### Trigésima e trigésima primeira extensões: faixas 0–5 e 6–11 do C0 3 000 199 222 471,5

Runs 43131497894 (faixas 0–5) e 43131501697 (faixas 6–11), pastas `de_3000199222471.5/faixas_0-5/` e `faixas_6-11/`;
colagem das 12 faixas em `de_3000199222471.5/juntas_0-11/`: as 12 colagens conferem (a faixa 0 recalcula
`N(3 000 199 222 471,5) = 12 363 255 684 117`, o fim da vigésima nona extensão), déficit 0 em todas,
`3 000 199 222 471,5 < Im s ≤ 3 000 200 662 471,5` com 6 163 151 zeros, todos na reta (maior raio 5,01·10⁻¹⁸).
Faixas 0–5: `N` de 12 363 255 684 117 a 12 363 258 765 692 (3 081 575 zeros). Faixas 6–11: `N` de 12 363 258 765 692 a
12 363 261 847 268 (3 081 576 zeros). Hipóteses nomeadas `JanelaContinuacao2026ad` e `JanelaContinuacao2026ae`. -/

/-- **Janela da trigésima extensão (fora do kernel)**: todos os zeros com
`3 000 199 222 471 < Im s ≤ 3 000 199 942 471` estão na reta. -/
def JanelaContinuacao2026ad : Prop := JanelaNaReta 3000199222471 3000199942471

/-- **Janela da trigésima primeira extensão (fora do kernel)**: todos os zeros com
`3 000 199 942 471 < Im s ≤ 3 000 200 662 471` estão na reta. -/
def JanelaContinuacao2026ae : Prop := JanelaNaReta 3000199942471 3000200662471

/-- RH até `3 000 199 942 471`, condicional a Platt–Trudgian e às janelas da Arb até a trigésima extensão. -/
theorem rhAteZ_continuacao30 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u) (hC22 : JanelaContinuacao2026v) (hC23 : JanelaContinuacao2026w)
    (hC24 : JanelaContinuacao2026x) (hC25 : JanelaContinuacao2026y) (hC26 : JanelaContinuacao2026z)
    (hC27 : JanelaContinuacao2026aa) (hC28 : JanelaContinuacao2026ab) (hC29 : JanelaContinuacao2026ac)
    (hC30 : JanelaContinuacao2026ad) : RHateZ 3000199942471 :=
  rhateZ_estende (rhAteZ_continuacao29 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22 hC23 hC24 hC25 hC26 hC27 hC28 hC29)
    (by exact_mod_cast hC30)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 199 942 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao30 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u) (hC22 : JanelaContinuacao2026v) (hC23 : JanelaContinuacao2026w)
    (hC24 : JanelaContinuacao2026x) (hC25 : JanelaContinuacao2026y) (hC26 : JanelaContinuacao2026z)
    (hC27 : JanelaContinuacao2026aa) (hC28 : JanelaContinuacao2026ab) (hC29 : JanelaContinuacao2026ac)
    (hC30 : JanelaContinuacao2026ad) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000199942471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima
    (rhAteZ_continuacao30 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22 hC23 hC24 hC25 hC26 hC27 hC28 hC29 hC30) h
  simpa using this

/-- **O par mais frágil das faixas 0–5** (zeros 12 363 258 136 141 e …142, `γ ≈ 3 000 199 795 378,9866`, a
0,00200166 um do outro, `s = 0,0086`): `−2,51·10⁻⁶ ≤ λ ≤ −2,00·10⁻⁶`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −2,003·10⁻⁶). -/
theorem par_mais_fragil_continuacao30 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300019979537898662560169197242 / 10 ^ 17| ≤ 454 / 10 ^ 20)
    (h₂ : |γ₂ - 300019979537898862727157906154 / 10 ^ 17| ≤ 290 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(251 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(200 : ℝ) / 100000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 200166 / 100000000) (hi := 200167 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-- RH até `3 000 200 662 471`, condicional a Platt–Trudgian e às janelas da Arb até a trigésima primeira extensão. -/
theorem rhAteZ_continuacao31 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u) (hC22 : JanelaContinuacao2026v) (hC23 : JanelaContinuacao2026w)
    (hC24 : JanelaContinuacao2026x) (hC25 : JanelaContinuacao2026y) (hC26 : JanelaContinuacao2026z)
    (hC27 : JanelaContinuacao2026aa) (hC28 : JanelaContinuacao2026ab) (hC29 : JanelaContinuacao2026ac)
    (hC30 : JanelaContinuacao2026ad) (hC31 : JanelaContinuacao2026ae) : RHateZ 3000200662471 :=
  rhateZ_estende (rhAteZ_continuacao30 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22 hC23 hC24 hC25 hC26 hC27 hC28 hC29 hC30)
    (by exact_mod_cast hC31)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 200 662 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao31 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u) (hC22 : JanelaContinuacao2026v) (hC23 : JanelaContinuacao2026w)
    (hC24 : JanelaContinuacao2026x) (hC25 : JanelaContinuacao2026y) (hC26 : JanelaContinuacao2026z)
    (hC27 : JanelaContinuacao2026aa) (hC28 : JanelaContinuacao2026ab) (hC29 : JanelaContinuacao2026ac)
    (hC30 : JanelaContinuacao2026ad) (hC31 : JanelaContinuacao2026ae) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000200662471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima
    (rhAteZ_continuacao31 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22 hC23 hC24 hC25 hC26 hC27 hC28 hC29 hC30 hC31) h
  simpa using this

/-- **O par mais frágil das faixas 6–11** (zeros 12 363 259 127 682 e …683, `γ ≈ 3 000 200 027 049,2121`, a
0,00149108 um do outro, `s = 0,0064`): `−1,39·10⁻⁶ ≤ λ ≤ −1,11·10⁻⁶`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −1,112·10⁻⁶). -/
theorem par_mais_fragil_continuacao31 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300020002704921214987889338254 / 10 ^ 17| ≤ 188 / 10 ^ 20)
    (h₂ : |γ₂ - 300020002704921364095894377780 / 10 ^ 17| ≤ 77 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(139 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(111 : ℝ) / 100000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 149108 / 100000000) (hi := 149109 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-! ### Trigésima segunda e trigésima terceira extensões: faixas 0–5 e 6–11 do C0 3 000 200 662 471,5

Runs 43158851648 (faixas 0–5) e 43158854801 (faixas 6–11), pastas `de_3000200662471.5/faixas_0-5/` e `faixas_6-11/`;
colagem das 12 faixas em `de_3000200662471.5/juntas_0-11/`: as 12 colagens conferem (a faixa 0 recalcula
`N(3 000 200 662 471,5) = 12 363 261 847 268`, o fim da trigésima primeira extensão), déficit 0 em todas,
`3 000 200 662 471,5 < Im s ≤ 3 000 202 102 471,5` com 6 163 152 zeros, todos na reta (maior raio 5,01·10⁻¹⁸).
Faixas 0–5: `N` de 12 363 261 847 268 a 12 363 264 928 844 (3 081 576 zeros). Faixas 6–11: `N` de 12 363 264 928 844 a
12 363 268 010 420 (3 081 576 zeros). Hipóteses nomeadas `JanelaContinuacao2026af` e `JanelaContinuacao2026ag`. -/

/-- **Janela da trigésima segunda extensão (fora do kernel)**: todos os zeros com
`3 000 200 662 471 < Im s ≤ 3 000 201 382 471` estão na reta. -/
def JanelaContinuacao2026af : Prop := JanelaNaReta 3000200662471 3000201382471

/-- **Janela da trigésima terceira extensão (fora do kernel)**: todos os zeros com
`3 000 201 382 471 < Im s ≤ 3 000 202 102 471` estão na reta. -/
def JanelaContinuacao2026ag : Prop := JanelaNaReta 3000201382471 3000202102471

/-- RH até `3 000 201 382 471`, condicional a Platt–Trudgian e às janelas da Arb até a trigésima segunda extensão. -/
theorem rhAteZ_continuacao32 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u) (hC22 : JanelaContinuacao2026v) (hC23 : JanelaContinuacao2026w)
    (hC24 : JanelaContinuacao2026x) (hC25 : JanelaContinuacao2026y) (hC26 : JanelaContinuacao2026z)
    (hC27 : JanelaContinuacao2026aa) (hC28 : JanelaContinuacao2026ab) (hC29 : JanelaContinuacao2026ac)
    (hC30 : JanelaContinuacao2026ad) (hC31 : JanelaContinuacao2026ae)
    (hC32 : JanelaContinuacao2026af) : RHateZ 3000201382471 :=
  rhateZ_estende (rhAteZ_continuacao31 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22 hC23 hC24 hC25 hC26 hC27 hC28 hC29 hC30 hC31)
    (by exact_mod_cast hC32)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 201 382 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao32 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u) (hC22 : JanelaContinuacao2026v) (hC23 : JanelaContinuacao2026w)
    (hC24 : JanelaContinuacao2026x) (hC25 : JanelaContinuacao2026y) (hC26 : JanelaContinuacao2026z)
    (hC27 : JanelaContinuacao2026aa) (hC28 : JanelaContinuacao2026ab) (hC29 : JanelaContinuacao2026ac)
    (hC30 : JanelaContinuacao2026ad) (hC31 : JanelaContinuacao2026ae)
    (hC32 : JanelaContinuacao2026af) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000201382471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima
    (rhAteZ_continuacao32 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22 hC23 hC24 hC25 hC26 hC27 hC28 hC29 hC30 hC31 hC32) h
  simpa using this

/-- **O par mais frágil das faixas 0–5** (zeros 12 363 263 577 244 e …245, `γ ≈ 3 000 201 066 674,7301`, a
0,00080860 um do outro, `s = 0,0035`): `−4,09·10⁻⁷ ≤ λ ≤ −3,26·10⁻⁷`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −3,269·10⁻⁷). -/
theorem par_mais_fragil_continuacao32 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300020106667473006073674240735 / 10 ^ 17| ≤ 199 / 10 ^ 20)
    (h₂ : |γ₂ - 300020106667473086934427469083 / 10 ^ 17| ≤ 30 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(409 : ℝ) / 1000000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(326 : ℝ) / 1000000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 80860 / 100000000) (hi := 80861 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-- RH até `3 000 202 102 471`, condicional a Platt–Trudgian e às janelas da Arb até a trigésima terceira extensão. -/
theorem rhAteZ_continuacao33 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u) (hC22 : JanelaContinuacao2026v) (hC23 : JanelaContinuacao2026w)
    (hC24 : JanelaContinuacao2026x) (hC25 : JanelaContinuacao2026y) (hC26 : JanelaContinuacao2026z)
    (hC27 : JanelaContinuacao2026aa) (hC28 : JanelaContinuacao2026ab) (hC29 : JanelaContinuacao2026ac)
    (hC30 : JanelaContinuacao2026ad) (hC31 : JanelaContinuacao2026ae)
    (hC32 : JanelaContinuacao2026af) (hC33 : JanelaContinuacao2026ag) : RHateZ 3000202102471 :=
  rhateZ_estende (rhAteZ_continuacao32 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22 hC23 hC24 hC25 hC26 hC27 hC28 hC29 hC30 hC31 hC32)
    (by exact_mod_cast hC33)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 202 102 471`** (condicional). -/
theorem primeiro_fora_acima_continuacao33 (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) (hC : JanelaContinuacao2026) (hC2 : JanelaContinuacao2026b)
    (hC3 : JanelaContinuacao2026c) (hC4 : JanelaContinuacao2026d) (hC5 : JanelaContinuacao2026e)
    (hC6 : JanelaContinuacao2026f) (hC7 : JanelaContinuacao2026g) (hC8 : JanelaContinuacao2026h)
    (hC9 : JanelaContinuacao2026i) (hC10 : JanelaContinuacao2026j) (hC11 : JanelaContinuacao2026k)
    (hC12 : JanelaContinuacao2026l) (hC13 : JanelaContinuacao2026m) (hC14 : JanelaContinuacao2026n)
    (hC15 : JanelaContinuacao2026o) (hC16 : JanelaContinuacao2026p) (hC17 : JanelaContinuacao2026q)
    (hC18 : JanelaContinuacao2026r) (hC19 : JanelaContinuacao2026s) (hC20 : JanelaContinuacao2026t)
    (hC21 : JanelaContinuacao2026u) (hC22 : JanelaContinuacao2026v) (hC23 : JanelaContinuacao2026w)
    (hC24 : JanelaContinuacao2026x) (hC25 : JanelaContinuacao2026y) (hC26 : JanelaContinuacao2026z)
    (hC27 : JanelaContinuacao2026aa) (hC28 : JanelaContinuacao2026ab) (hC29 : JanelaContinuacao2026ac)
    (hC30 : JanelaContinuacao2026ad) (hC31 : JanelaContinuacao2026ae)
    (hC32 : JanelaContinuacao2026af) (hC33 : JanelaContinuacao2026ag) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000202102471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima
    (rhAteZ_continuacao33 hPT hJ hC hC2 hC3 hC4 hC5 hC6 hC7 hC8 hC9 hC10 hC11 hC12 hC13 hC14 hC15 hC16 hC17 hC18 hC19 hC20 hC21 hC22 hC23 hC24 hC25 hC26 hC27 hC28 hC29 hC30 hC31 hC32 hC33) h
  simpa using this

/-- **O par mais frágil das faixas 6–11** (zeros 12 363 265 827 917 e …918, `γ ≈ 3 000 201 592 536,8547`, a
0,00176491 um do outro, `s = 0,0076`): `−1,95·10⁻⁶ ≤ λ ≤ −1,55·10⁻⁶`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV
calculado: −1,558·10⁻⁶). -/
theorem par_mais_fragil_continuacao33 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 300020159253685467131915860866 / 10 ^ 17| ≤ 91 / 10 ^ 20)
    (h₂ : |γ₂ - 300020159253685643623350133745 / 10 ^ 17| ≤ 352 / 10 ^ 20)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(195 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(155 : ℝ) / 100000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 176491 / 100000000) (hi := 176492 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

end ClayRiemannProof.Continuacao
