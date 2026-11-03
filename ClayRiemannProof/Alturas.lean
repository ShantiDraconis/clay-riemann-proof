import ClayRiemannProof.Lehmer

/-!
# Os pares mais frágeis das janelas certificadas em 10¹⁴, 10¹⁶ e 10¹⁷

O workflow `alturas.yml` (run 41588835957, branch `resultados-alturas`) certificou com a Arb três janelas de 20 000
zeros cada, em `10¹⁴`, `10¹⁶` e `10¹⁷`: todos os zeros na reta, `N(T_a)` e `N(T_b)` pela contagem de Turing
intervalar, a contagem fechando e as bolas disjuntas. Em cada janela, o par de zeros consecutivos mais próximo dá,
com as bolas da Arb como hipótese, uma faixa para o tempo `λ` em que o fluxo do calor de de Bruijn faz os dois
colidirem (coordenadas `x = 2γ`, molde de `ClayRiemannProof.Continuacao.par_mais_fragil_continuacao`):

* `par_mais_fragil_1e14`: zeros 467 888 702 924 344 e …345, a 0,006680 um do outro (`s = 0,0323`):
  `−2,79·10⁻⁵ ≤ λ ≤ −2,23·10⁻⁵`;
* `par_mais_fragil_1e16`: zeros 54 118 226 280 296 885 e …886, a 0,0013949 um do outro (`s = 0,0078`, um quinto do
  mínimo esperado pelo GUE em 20 000 zeros): `−1,22·10⁻⁶ ≤ λ ≤ −9,72·10⁻⁷`;
* `par_mais_fragil_1e17`: zeros 577 829 042 746 908 883 e …884, a 0,006754 um do outro (`s = 0,0401`):
  `−2,86·10⁻⁵ ≤ λ ≤ −2,28·10⁻⁵`.

Em `10¹⁸` a Arb achou os 20 002 zeros (10 891 s), mas a contagem de Turing em `T_b` passou do limite de 3 580 s por
chamada; sem a contagem a janela não fecha e a lista não foi gravada, por isso não há teorema para `10¹⁸` aqui (o par
da 1ª onda da fronteira em `10¹⁸` está em `Continuacao.par_mais_fragil_1e18`).

As bolas são cálculos fora do kernel (hipóteses). Nada aqui prova ou refuta RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Alturas

open ClayRiemannProof.Lehmer

/-- **O par mais frágil da janela em 10¹⁴** (zeros 467 888 702 924 344 e …345, `γ ≈ 10¹⁴ + 1 935,048`):
`−2,79·10⁻⁵ ≤ λ ≤ −2,23·10⁻⁵`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV calculado: −2,2325·10⁻⁵). -/
theorem par_mais_fragil_1e14 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 100000000001935047610639720963493382137382477029 / 10 ^ 33| ≤ 551 / 10 ^ 37)
    (h₂ : |γ₂ - 100000000001935054290860521132031930477980765998 / 10 ^ 33| ≤ 281 / 10 ^ 36)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(279 : ℝ) / 10000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(223 : ℝ) / 10000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 668022 / 100000000) (hi := 668023 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-- **O par mais frágil da janela em 10¹⁶** (zeros 54 118 226 280 296 885 e …886, `γ ≈ 10¹⁶ + 791,214`):
`−1,22·10⁻⁶ ≤ λ ≤ −9,72·10⁻⁷`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV calculado: −9,729·10⁻⁷). -/
theorem par_mais_fragil_1e16 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 10000000000000791214308291153064663442 / 10 ^ 21| ≤ 234 / 10 ^ 24)
    (h₂ : |γ₂ - 100000000000007912157031744287971521981 / 10 ^ 22| ≤ 908 / 10 ^ 25)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(122 : ℝ) / 100000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(972 : ℝ) / 1000000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 139488 / 100000000) (hi := 139489 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

/-- **O par mais frágil da janela em 10¹⁷** (zeros 577 829 042 746 908 883 e …884, `γ ≈ 10¹⁷ + 2 143,769`):
`−2,86·10⁻⁵ ≤ λ ≤ −2,28·10⁻⁵`, qualquer que seja `g` com `Δ²g ≤ 4/5` (CSV calculado: −2,2829·10⁻⁵). -/
theorem par_mais_fragil_1e17 {γ₁ γ₂ g : ℝ}
    (h₁ : |γ₁ - 1000000000000021437687036110507199367301300262 / 10 ^ 28| ≤ 441 / 10 ^ 31)
    (h₂ : |γ₂ - 1000000000000021437754574566286302740289786409 / 10 ^ 28| ≤ 483 / 10 ^ 31)
    (hg : 0 < g) (hq : (2 * (γ₂ - γ₁)) ^ 2 * g ≤ 4 / 5) :
    -(286 : ℝ) / 10000000 ≤ csv (2 * (γ₂ - γ₁)) g ∧ csv (2 * (γ₂ - γ₁)) g ≤ -(228 : ℝ) / 10000000 := by
  obtain ⟨hlo, hhi⟩ := dif_bolas h₁ h₂
  obtain ⟨c1, c2⟩ := csv_por_distancia (lo := 675384 / 100000000) (hi := 675385 / 100000000)
    (by norm_num) (le_trans (by norm_num) hlo) (le_trans hhi (by norm_num)) hg hq
  exact ⟨le_trans (by norm_num) c1, le_trans c2 (by norm_num)⟩

end ClayRiemannProof.Alturas
