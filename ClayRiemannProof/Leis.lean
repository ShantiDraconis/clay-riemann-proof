import ClayRiemannProof.PrimeiroFora
import ClayRiemannProof.Bridges
import ClayRiemannProof.Colisao

/-!
# As leis por trás dos gráficos: `S(t)`, Gram e Rosser; unidades do fluxo de de Bruijn; matrizes; produto; habitantes

Os gráficos da faixa certificada (aglomerados, vazios, Gram triplo, Rosser, `S(t)` extremo, pares frágeis) obedecem a
leis exatas. Este arquivo as prova.

* **`S(t)`**: com `N(t) = N₀ + #{γ ≤ t}` e `S(t) = N(t) − θ(t)/π − 1`, vale a lei mestra
  `S(t₂) − S(t₁) = #{zeros em (t₁, t₂]} − (θ(t₂) − θ(t₁))/π` (`lei_mestra`).
  * Num **vazio** `S` desce (`lei_vazio`), em vez de ficar parado.
  * Nos pontos de Gram (`θ(g) = mπ`) `S` é inteiro (`S_gram`). Entre `g_m` e `g_{m+k}`, `S` sobe o número de zeros e
    desce `k` (`lei_gram`).
  * Daí saem o **vazio de `k` intervalos** (`S` desce exatamente `k`), o **Gram triplo** (`S` sobe 2) e o **bloco de
    Rosser** (`S` igual nas pontas ⟺ exatamente `k` zeros).
  * O padrão da violação de Rosser da faixa (3 zeros num intervalo e 0 nos 2 seguintes) devolve `S` ao valor
    inicial (`aglomerado_e_vazio`).
* **Unidades do fluxo de de Bruijn**: `H₀(z) = ξ(½ + iz/2)/8`, logo `Re s − ½ = −Im z/2` (`re_s_de_z`). Dois zeros de
  `ζ` a distância `Δγ` estão a `2Δγ` na variável `z`, e o modelo colide em `t = −Δγ²/2` (`colisao_em_gama`).
  * Para o par mais frágil, `Δγ = 0,007987`, isso dá `−3,1896·10⁻⁵`, o `λ` da tabela
    (`colisao_par_mais_fragil`).
  * Antes do limiar não há deslocamento: em `t = −2·10⁻⁵` o par ainda está na reta (`sem_deslocamento_em_2e5`).
  * Depois do limiar, o deslocamento é `√(−Δγ² − 2t)/2` (`deslocamento_forcado`).
* **Matrizes**: no vetor `(Re s − ½, Im s)`, tensão, espelho e torção são as matrizes `diag(−1, −1)`, `diag(1, −1)` e
  `diag(−1, 1)`. Elas formam o grupo de Klein (`vec_*`, `klein`).
* **Produto do quarteto**: `(w − z)(w + z)(w − z̄)(w + z̄) = w⁴ − 2 Re(z²) w² + |z|⁴`, com coeficientes reais
  (`produto_quarteto`). Na reta (`Re z = 0`), o produto é o quadrado perfeito `(w² + t²)²`, um par duplo
  (`produto_na_reta`).
* **Habitantes**: com `Fora = {zeros não triviais com Re ≠ ½}`:
  * Clay ⟺ `Fora = ∅` (`target_iff_fora_vazio`);
  * `Fora` é vazio ou tem pelo menos 4 habitantes (`fora_vazio_ou_quatro`);
  * as órbitas têm só as classes 2 e 4 (`classes_orbita`);
  * não há habitantes até a altura 13 (`sem_habitantes_ate_13`);
  * com as hipóteses nomeadas, `Fora` não tem habitantes até `3 000 175 342 471` (`fora_ate_janela_vazio`).

Nada aqui prova RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Leis

open Complex ComplexConjugate Set Matrix ClayRiemannProof.Zeta.Symmetry ClayRiemannProof.Bridges
  ClayRiemannProof.FiniteWorlds

/-! ## 1. `S(t)`, Gram e Rosser -/

section Contagem

variable (N₀ : ℤ) (Γ : Finset ℝ) (θ : ℝ → ℝ)

/-- `N(t) = N₀ + #{γ ∈ Γ : γ ≤ t}`. -/
noncomputable def contagem (t : ℝ) : ℤ := N₀ + ((Γ.filter (· ≤ t)).card : ℤ)

/-- `S(t) = N(t) − θ(t)/π − 1`. -/
noncomputable def S (t : ℝ) : ℝ := (contagem N₀ Γ t : ℝ) - θ t / Real.pi - 1

/-- Número de zeros em `(t₁, t₂]`. -/
noncomputable def entre (t₁ t₂ : ℝ) : ℕ := (Γ.filter (fun γ => t₁ < γ ∧ γ ≤ t₂)).card

theorem card_split {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    (Γ.filter (· ≤ t₂)).card = (Γ.filter (· ≤ t₁)).card + entre Γ t₁ t₂ := by
  unfold entre
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext γ
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hγ, h2⟩
      by_cases h1 : γ ≤ t₁
      · exact Or.inl ⟨hγ, h1⟩
      · exact Or.inr ⟨hγ, lt_of_not_ge h1, h2⟩
    · rintro (⟨hγ, h1⟩ | ⟨hγ, -, h2⟩)
      · exact ⟨hγ, h1.trans h⟩
      · exact ⟨hγ, h2⟩
  · rw [Finset.disjoint_filter]
    intro γ _ h1 h2
    linarith [h2.1]

/-- **Lei mestra**: `S(t₂) − S(t₁) = #{zeros em (t₁, t₂]} − (θ(t₂) − θ(t₁))/π`. -/
theorem lei_mestra {t₁ t₂ : ℝ} (h : t₁ ≤ t₂) :
    S N₀ Γ θ t₂ - S N₀ Γ θ t₁ = (entre Γ t₁ t₂ : ℝ) - (θ t₂ - θ t₁) / Real.pi := by
  unfold S contagem
  rw [card_split Γ h]
  push_cast
  ring

/-- **Lei do vazio**: sem zeros em `(t₁, t₂]`, `S` desce exatamente `(θ(t₂) − θ(t₁))/π`; um vazio nunca segura `S`. -/
theorem lei_vazio (hθ : StrictMono θ) {t₁ t₂ : ℝ} (h : t₁ < t₂) (hv : entre Γ t₁ t₂ = 0) :
    S N₀ Γ θ t₂ - S N₀ Γ θ t₁ = -(θ t₂ - θ t₁) / Real.pi ∧ S N₀ Γ θ t₂ < S N₀ Γ θ t₁ := by
  have hm := lei_mestra N₀ Γ θ h.le
  rw [hv] at hm
  push_cast at hm
  have hd : 0 < (θ t₂ - θ t₁) / Real.pi := div_pos (sub_pos.mpr (hθ h)) Real.pi_pos
  constructor
  · rw [hm]
    ring
  · linarith

/-- Nos pontos de Gram (`θ(g) = mπ`), `S(g) = N(g) − m − 1` é inteiro. -/
theorem S_gram {g : ℝ} {m : ℤ} (hg : θ g = m * Real.pi) :
    S N₀ Γ θ g = ((contagem N₀ Γ g - m - 1 : ℤ) : ℝ) := by
  unfold S
  rw [hg, mul_div_assoc, div_self Real.pi_ne_zero, mul_one]
  push_cast
  ring

/-- **Lei de Gram**: entre `g_m` e `g_{m+k}`, `S` sobe o número de zeros e desce `k`. -/
theorem lei_gram {g₁ g₂ : ℝ} {m k : ℤ} (h : g₁ ≤ g₂) (h1 : θ g₁ = m * Real.pi)
    (h2 : θ g₂ = (m + k) * Real.pi) :
    S N₀ Γ θ g₂ - S N₀ Γ θ g₁ = (entre Γ g₁ g₂ : ℝ) - k := by
  rw [lei_mestra N₀ Γ θ h, h1, h2]
  field_simp
  ring

/-- **Vazio de `k` intervalos de Gram**: sem zeros, `S` desce exatamente `k`. -/
theorem vazio_gram {g₁ g₂ : ℝ} {m k : ℤ} (h : g₁ ≤ g₂) (h1 : θ g₁ = m * Real.pi)
    (h2 : θ g₂ = (m + k) * Real.pi) (hv : entre Γ g₁ g₂ = 0) :
    S N₀ Γ θ g₂ = S N₀ Γ θ g₁ - k := by
  have := lei_gram N₀ Γ θ h h1 h2
  rw [hv] at this
  push_cast at this
  linarith

/-- **Gram triplo**: três zeros num só intervalo de Gram fazem `S` subir 2. -/
theorem gram_triplo {g₁ g₂ : ℝ} {m : ℤ} (h : g₁ ≤ g₂) (h1 : θ g₁ = m * Real.pi)
    (h2 : θ g₂ = (m + 1) * Real.pi) (h3 : entre Γ g₁ g₂ = 3) :
    S N₀ Γ θ g₂ = S N₀ Γ θ g₁ + 2 := by
  have := lei_gram N₀ Γ θ h h1 (k := 1) (by rw [h2]; push_cast; ring)
  rw [h3] at this
  push_cast at this
  linarith

/-- **Bloco de Rosser**: `S` igual nas pontas de um bloco de `k` intervalos ⟺ o bloco tem exatamente `k` zeros. -/
theorem rosser_bloco {g₁ g₂ : ℝ} {m : ℤ} {k : ℕ} (h : g₁ ≤ g₂) (h1 : θ g₁ = m * Real.pi)
    (h2 : θ g₂ = (m + k) * Real.pi) :
    S N₀ Γ θ g₂ = S N₀ Γ θ g₁ ↔ entre Γ g₁ g₂ = k := by
  have := lei_gram N₀ Γ θ h h1 h2
  push_cast at this
  constructor
  · intro he
    have : (entre Γ g₁ g₂ : ℝ) = k := by linarith
    exact_mod_cast this
  · intro he
    rw [he] at this
    linarith

/-- **Aglomerado + vazio**: três zeros num intervalo de Gram e nenhum nos dois seguintes devolvem `S` ao valor
inicial. É o padrão da violação de Rosser da faixa certificada (bloco de 1 intervalo com 3 zeros, depois bloco de
2 com 0). -/
theorem aglomerado_e_vazio {g₁ g₂ g₃ : ℝ} {m : ℤ} (h12 : g₁ ≤ g₂) (h23 : g₂ ≤ g₃)
    (h1 : θ g₁ = m * Real.pi) (h2 : θ g₂ = (m + 1) * Real.pi) (h3 : θ g₃ = (m + 3) * Real.pi)
    (e1 : entre Γ g₁ g₂ = 3) (e2 : entre Γ g₂ g₃ = 0) :
    S N₀ Γ θ g₃ = S N₀ Γ θ g₁ := by
  have a := gram_triplo N₀ Γ θ h12 h1 h2 e1
  have b := vazio_gram N₀ Γ θ h23 (m := m + 1) (k := 2) (by rw [h2]; push_cast; ring)
    (by rw [h3]; push_cast; ring) e2
  push_cast at b
  linarith

end Contagem

/-! ## 2. Unidades do fluxo de de Bruijn -/

/-- Com `s = ½ + iz/2` (`H₀(z) = ξ(½ + iz/2)/8`): `Re s − ½ = −Im z/2`. -/
theorem re_s_de_z (z : ℂ) : ((1 : ℂ) / 2 + I * z / 2).re - 1 / 2 = -(z.im / 2) := by
  simp
  ring

/-- `Im s = Re z/2`: a ordenada `γ` de um zero é metade da sua posição `x = 2γ` na variável `z`. -/
theorem im_s_de_z (z : ℂ) : ((1 : ℂ) / 2 + I * z / 2).im = z.re / 2 := by
  simp

/-- **Colisão em unidades de `γ`**: dois zeros a distância `Δγ` estão a `2Δγ` em `z`; o par isolado colide em
`t = −Δγ²/2`. -/
theorem colisao_em_gama (Δγ t : ℝ) :
    (∀ z : ℂ, Colisao.H2 Δγ t z = 0 → z.im = 0) ↔ -(Δγ ^ 2) / 2 ≤ t :=
  Colisao.zeros_reais_iff Δγ t

/-- O mesmo pela distância em `z`: `Δ = 2Δγ` em `Colisao.colisao` dá `−(2Δγ)²/8 = −Δγ²/2`. -/
theorem colisao_em_gama' (Δγ t : ℝ) :
    (∀ z : ℂ, Colisao.H2 (2 * Δγ / 2) t z = 0 → z.im = 0) ↔ -(Δγ ^ 2) / 2 ≤ t := by
  rw [Colisao.colisao]
  constructor <;> intro h <;> nlinarith

/-- **O par mais frágil** (`Δγ = 0,007987`): colisão do modelo em `t = −63 792 169/(2·10¹²) = −3,1896…·10⁻⁵`, o mesmo
`λ` da tabela (`−3,19·10⁻⁵`); a correção dos vizinhos é de ordem `Δ⁴g`. -/
theorem colisao_par_mais_fragil :
    -((7987 / 1000000 : ℝ) ^ 2) / 2 = -(63792169 / 2000000000000) ∧
      -(32 / 1000000 : ℝ) < -((7987 / 1000000 : ℝ) ^ 2) / 2 ∧
      -((7987 / 1000000 : ℝ) ^ 2) / 2 < -(31 / 1000000) := by
  norm_num

/-- **Sem deslocamento antes do limiar**: para `t ≥ −Δγ²/2`, todo zero do modelo está na reta (`Re s = ½`). -/
theorem sem_deslocamento {Δγ t : ℝ} (ht : -(Δγ ^ 2) / 2 ≤ t) :
    ∀ z : ℂ, Colisao.H2 Δγ t z = 0 → ((1 : ℂ) / 2 + I * z / 2).re = 1 / 2 := by
  intro z hz
  have him := (colisao_em_gama Δγ t).mpr ht z hz
  have := re_s_de_z z
  rw [him] at this
  linarith

/-- Para o par mais frágil, em `t = −2·10⁻⁵` o modelo ainda tem os dois zeros na reta (deslocamento 0). -/
theorem sem_deslocamento_em_2e5 :
    ∀ z : ℂ, Colisao.H2 (7987 / 1000000) (-(2 / 100000)) z = 0 →
      ((1 : ℂ) / 2 + I * z / 2).re = 1 / 2 :=
  sem_deslocamento (by norm_num)

/-- **Deslocamento forçado** depois do limiar (`t ≤ −Δγ²/2`): o zero do modelo em `z = i√(−Δγ² − 2t)` tem
`Re s − ½ = −√(−Δγ² − 2t)/2`. -/
theorem deslocamento_forcado (Δγ t : ℝ) (ht : t ≤ -(Δγ ^ 2) / 2) :
    ∃ z : ℂ, Colisao.H2 Δγ t z = 0 ∧
      ((1 : ℂ) / 2 + I * z / 2).re - 1 / 2 = -(Real.sqrt (2 * (-(Δγ ^ 2) / 2 - t)) / 2) :=
  ⟨_, (Colisao.raiz_quadrada Δγ t ht).1, by rw [re_s_de_z, (Colisao.raiz_quadrada Δγ t ht).2]⟩

/-! ## 3. Os operadores como matrizes -/

/-- O vetor de desvio `(Re s − ½, Im s)`. -/
noncomputable def vec (s : ℂ) : Fin 2 → ℝ := ![s.re - 1 / 2, s.im]

def Mtensao : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 0; 0, -1]
def Mespelho : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
def Mtorcao : Matrix (Fin 2) (Fin 2) ℝ := !![-1, 0; 0, 1]

theorem vec_tensao (s : ℂ) : vec (tensao s) = Mtensao *ᵥ vec s := by
  ext i
  fin_cases i
  · simp [vec, Mtensao, tensao, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp [vec, Mtensao, tensao, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem vec_espelho (s : ℂ) : vec (espelho s) = Mespelho *ᵥ vec s := by
  ext i
  fin_cases i <;> simp [vec, Mespelho, espelho, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem vec_torcao (s : ℂ) : vec (torcao s) = Mtorcao *ᵥ vec s := by
  ext i
  fin_cases i
  · simp [vec, Mtorcao, torcao, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp [vec, Mtorcao, torcao, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- **Grupo de Klein**: cada operador é uma involução e o produto de dois é o terceiro. -/
theorem klein :
    Mtensao * Mtensao = 1 ∧ Mespelho * Mespelho = 1 ∧ Mtorcao * Mtorcao = 1 ∧
      Mespelho * Mtensao = Mtorcao ∧ Mtensao * Mespelho = Mtorcao ∧ Mtensao * Mtorcao = Mespelho ∧
      Mtorcao * Mespelho = Mtensao := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Mtensao, Mespelho, Mtorcao, Matrix.one_fin_two]

/-! ## 4. O produto do quarteto -/

/-- **Produto do quarteto**: `(w − z)(w + z)(w − z̄)(w + z̄) = w⁴ − 2 Re(z²) w² + |z|⁴`, um polinômio par de
coeficientes reais. -/
theorem produto_quarteto (z w : ℂ) :
    (w - z) * (w + z) * (w - conj z) * (w + conj z) =
      w ^ 4 - 2 * ((z ^ 2).re : ℂ) * w ^ 2 + (normSq z : ℂ) ^ 2 := by
  have h1 : z ^ 2 + conj z ^ 2 = 2 * ((z ^ 2).re : ℂ) := by
    rw [← map_pow, Complex.add_conj]
    push_cast
    ring
  have h2 : z * conj z = (normSq z : ℂ) := Complex.mul_conj z
  linear_combination (-(w ^ 2)) * h1 + (z * conj z + (normSq z : ℂ)) * h2

/-- **Na reta o quarteto vira par duplo**: com `Re z = 0` (`z = it`), o produto é `(w² + t²)²`. -/
theorem produto_na_reta {z : ℂ} (hz : z.re = 0) (w : ℂ) :
    (w - z) * (w + z) * (w - conj z) * (w + conj z) = (w ^ 2 + (z.im : ℂ) ^ 2) ^ 2 := by
  rw [produto_quarteto]
  have hre : (z ^ 2).re = -(z.im ^ 2) := by simp [sq, hz]
  have hn : normSq z = z.im ^ 2 := by rw [normSq_apply, hz]; ring
  rw [hre, hn]
  push_cast
  ring

/-! ## 5. Habitantes e inabitantes -/

/-- Os zeros não triviais fora da reta. -/
def Fora : Set ℂ := {s | s ∈ Z ∧ s.re ≠ 1 / 2}

/-- **Clay ⟺ `Fora` não tem habitantes.** -/
theorem target_iff_fora_vazio : Target ↔ Fora = ∅ := by
  constructor
  · intro hT
    ext s
    simp only [Fora, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
    exact fun hs => riemann_imp_re hT hs
  · intro h
    refine riemann_iff_torcao.mpr fun s hs => (torcao_fixo_iff s).mpr ?_
    by_contra hne
    have : s ∈ Fora := ⟨hs, hne⟩
    rw [h] at this
    exact this

/-- A órbita de um habitante de `Fora` fica toda em `Fora`. -/
theorem orbita_sub_fora {s : ℂ} (hs : s ∈ Fora) : (↑(orbita s) : Set ℂ) ⊆ Fora := by
  classical
  obtain ⟨hz, hre⟩ := hs
  intro x hx
  simp only [orbita, Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨hz, hre⟩
  · exact ⟨espelho_mem_Z hz, by simpa [espelho] using hre⟩
  · refine ⟨tensao_mem_Z hz, ?_⟩
    rw [re_tensao]
    intro h
    exact hre (by linarith)
  · refine ⟨torcao_mem_Z hz, ?_⟩
    rw [re_torcao]
    intro h
    exact hre (by linarith)

/-- **`Fora` é vazio ou tem pelo menos 4 habitantes.** -/
theorem fora_vazio_ou_quatro : Fora = ∅ ∨ 4 ≤ Fora.encard := by
  rcases Set.eq_empty_or_nonempty Fora with h | ⟨s, hs⟩
  · exact Or.inl h
  · right
    have h4 := card_orbita_fora hs.1 hs.2
    calc (4 : ℕ∞) = ((↑(orbita s) : Set ℂ)).encard := by
          rw [Set.encard_coe_eq_coe_finsetCard, h4]
          rfl
      _ ≤ Fora.encard := Set.encard_le_encard (orbita_sub_fora hs)

/-- **Classes de órbita**: só 2 (na reta) ou 4 (fora). -/
theorem classes_orbita {s : ℂ} (hs : s ∈ Z) : (orbita s).card = 2 ∨ (orbita s).card = 4 := by
  by_cases h : s.re = 1 / 2
  · exact Or.inl (card_orbita_reta hs h)
  · exact Or.inr (card_orbita_fora hs h)

/-- **Sem habitantes até a altura 13**: nenhum zero não trivial tem `|Im s| ≤ 13` (`HeightThirteen`). -/
theorem sem_habitantes_ate_13 : {s ∈ Z | |s.im| ≤ 13} = ∅ := by
  ext s
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_le]
  exact fun hs => PrimeiroFora.im_gt_13 hs

/-- **`Fora` sem habitantes até `3 000 175 342 471`**, condicional a Platt–Trudgian e à janela da Arb. -/
theorem fora_ate_janela_vazio (hPT : PlattTrudgian2021) (hJ : PrimeiroFora.JanelaArb2026) :
    {s ∈ Fora | |s.im| ≤ 3000175342471} = ∅ := by
  ext s
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
  intro hs him
  have hW := PrimeiroFora.rhAteZ_janela hPT hJ
  have hz := hs.1
  exact hs.2 (hW s hz.1 ((mem_Z_iff_nao_trivial s).mp hz).2
    (fun h1 => by rw [h1] at hz; exact absurd hz.2.2 (by simp)) (by exact_mod_cast him))

end ClayRiemannProof.Leis
