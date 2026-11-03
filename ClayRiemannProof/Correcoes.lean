import ClayRiemannProof.Leis
import ClayRiemannProof.Paridade
import ClayRiemannProof.Fronteira.Ht

/-!
# As correções no kernel: cada afirmação errada dos gráficos, com o teorema que a decide

Os gráficos e textos colados nesta fase (3/11/2026) traziam afirmações sobre como um zero fora da reta apareceria,
quanto um par precisaria ser empurrado e onde estaria o fechamento. Este arquivo prova, para cada uma, o enunciado
correto. Os números da Arb entram como hipóteses nomeadas, como em todo o repositório.

1. **Como um par fora da reta aparece na contagem** (`par_fora_na_janela`, `S_sobe_no_par`, `par_fora_da_caixa`).
   Um par `ρ, 1 − ρ̄` sozinho numa janela conta **2** em `N(T₂) − N(T₁)` e **0** na reta: déficit exatamente 2.
   `S = N − θ/π − 1` **sobe** (entre 0 e 2), não desce 2. Com `|Re ρ − ½| < 1/100`, nenhum dos dois está na faixa
   `0,51 ≤ Re s ≤ 0,99`.
2. **O deslocamento forçado do par #6** (`Δγ = 0,007987`; `bForcado`). Na colisão (`t = −Δγ²/2`) o desvio é **0**,
   não 0,00245. Depois dela, `b(t) = √(2(−Δγ²/2 − t))/2` vale `0,0030…` em `t = −5·10⁻⁵`, `0,0058…` em `−10⁻⁴` e
   `0,0091…` em `−2·10⁻⁴`; em `−10⁻⁴` não é 0,00678.
3. **de Bruijn–Newman** (`rh_iff_lambda_zero`, `lambda_negativo_impossivel`, `cota_de_lehmer_mais_fraca`). Com
   Rodgers–Tao (`Λ ≥ 0`, enunciado nomeado): RH ⟺ `Λ = 0`; `Λ < 0` é impossível ("Λ → 0⁻" não existe); e qualquer
   cota `λ < 0` vinda de um par de Lehmer é estritamente mais fraca que `Λ ≥ 0`.
4. **Gram com `j` zeros num intervalo** (`gram_k_zeros`, `gram_quadruplo`): `S` sobe `j − 1`; o intervalo com 4 zeros
   da continuação faz `S` subir 3.
5. **A janela da continuação a partir das contagens da Arb** (`continuacao_de_contagens`,
   `janelaContinuacao_de_contagens`, `rhAteZ_de_contagens`). A hipótese `Continuacao.JanelaContinuacao2026` deixa de
   ser primitiva: sai das quatro contagens exatas `N(b) − N(a)` (513 596, 513 596, 513 595, 513 596) e dos zeros
   achados na reta em cada faixa, mais a fatia `(…342 471; …342 471,5]` da seção 13.

Nada aqui prova RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Correcoes

open Complex Set ClayRiemannProof.Zeta.Symmetry ClayRiemannProof.FiniteWorlds

/-! ## 1. Como um par fora da reta aparece na contagem -/

/-- **Um par fora da reta sozinho numa janela**: a janela tem exatamente 2 zeros e nenhum na reta. Déficit 2, nunca 1. -/
theorem par_fora_na_janela {T₁ T₂ : ℝ} {ρ : ℂ} (hρ : ρ ∈ Paridade.Fora T₁ T₂)
    (hso : ∀ s ∈ Paridade.NaJanela T₁ T₂, s = ρ ∨ s = torcao ρ) :
    (Paridade.NaJanela T₁ T₂).ncard = 2 ∧ (Paridade.NaReta T₁ T₂).ncard = 0 := by
  have ht := Paridade.torcao_fora hρ
  have hj : Paridade.NaJanela T₁ T₂ = {ρ, torcao ρ} := by
    ext s
    simp only [mem_insert_iff, mem_singleton_iff]
    constructor
    · exact hso s
    · rintro (rfl | rfl)
      · exact hρ.1
      · exact ht.1
  have hr : Paridade.NaReta T₁ T₂ = ∅ := by
    ext s
    simp only [mem_empty_iff_false, iff_false]
    intro hs
    rcases hso s hs.1 with rfl | rfl
    · exact hρ.2 hs.2
    · exact ht.2 hs.2
  refine ⟨?_, by rw [hr, Set.ncard_empty]⟩
  rw [hj]
  exact Set.ncard_pair (Paridade.torcao_ne hρ).symm

/-- **`S` sobe no par**: se `N` sobe 2 numa janela em que `θ` anda menos que `2π`, `S = N − θ/π − 1` sobe (entre 0 e
2). Um par fora da reta não faz `S` descer 2. -/
theorem S_sobe_no_par {N₁ N₂ θ₁ θ₂ : ℝ} (hN : N₂ = N₁ + 2) (hθ : θ₁ ≤ θ₂) (hθ2 : θ₂ - θ₁ < 2 * Real.pi) :
    0 < (N₂ - θ₂ / Real.pi - 1) - (N₁ - θ₁ / Real.pi - 1) ∧
      (N₂ - θ₂ / Real.pi - 1) - (N₁ - θ₁ / Real.pi - 1) ≤ 2 := by
  have hpi := Real.pi_pos
  have e : (N₂ - θ₂ / Real.pi - 1) - (N₁ - θ₁ / Real.pi - 1) = 2 - (θ₂ - θ₁) / Real.pi := by
    rw [hN]
    field_simp
    ring
  have h1 : (θ₂ - θ₁) / Real.pi < 2 := by rw [div_lt_iff₀ hpi]; linarith
  have h0 : 0 ≤ (θ₂ - θ₁) / Real.pi := div_nonneg (by linarith) hpi.le
  rw [e]
  constructor <;> linarith

/-- **Fora da caixa `[0,51; 0,99]`**: com `|Re ρ − ½| < 1/100`, nem `ρ` nem `1 − ρ̄` têm `0,51 ≤ Re ≤ 0,99`. -/
theorem par_fora_da_caixa {ρ : ℂ} (hb : |ρ.re - 1 / 2| < 1 / 100) :
    ¬ (51 / 100 ≤ ρ.re ∧ ρ.re ≤ 99 / 100) ∧ ¬ (51 / 100 ≤ (torcao ρ).re ∧ (torcao ρ).re ≤ 99 / 100) := by
  rw [abs_lt] at hb
  rw [re_torcao]
  constructor <;> rintro ⟨h1, -⟩ <;> linarith [hb.1, hb.2]

/-! ## 2. O deslocamento forçado do par #6 -/

/-- O desvio `b(t) = |Re s − ½|` do zero do modelo de colisão depois do limiar: `√(2(−Δγ²/2 − t))/2`. -/
noncomputable def bForcado (Δγ t : ℝ) : ℝ := Real.sqrt (2 * (-(Δγ ^ 2) / 2 - t)) / 2

/-- É o desvio de `Leis.deslocamento_forcado`: `Re s − ½ = −b(t)`. -/
theorem bForcado_eh_desvio (Δγ t : ℝ) (ht : t ≤ -(Δγ ^ 2) / 2) :
    ∃ z : ℂ, Colisao.H2 Δγ t z = 0 ∧ ((1 : ℂ) / 2 + I * z / 2).re - 1 / 2 = -bForcado Δγ t :=
  Leis.deslocamento_forcado Δγ t ht

/-- **Na colisão o desvio é zero.** -/
theorem b_na_colisao (Δγ : ℝ) : bForcado Δγ (-(Δγ ^ 2) / 2) = 0 := by
  simp [bForcado]

/-- Faixa de `√X/2` por quadrados. -/
theorem metade_raiz_entre {X lo hi : ℝ} (hlo0 : 0 ≤ lo) (hlo : (2 * lo) ^ 2 < X) (hhi0 : 0 < hi)
    (hhi : X < (2 * hi) ^ 2) : lo < Real.sqrt X / 2 ∧ Real.sqrt X / 2 < hi := by
  have a := (Real.lt_sqrt (by linarith : (0 : ℝ) ≤ 2 * lo)).mpr hlo
  have b := (Real.sqrt_lt' (by linarith : (0 : ℝ) < 2 * hi)).mpr hhi
  constructor <;> linarith

/-- **O par #6 forçado** (`Δγ = 0,007987`): `b(−5·10⁻⁵) ∈ (0,0030; 0,0031)`, `b(−10⁻⁴) ∈ (0,0058; 0,0059)`,
`b(−2·10⁻⁴) ∈ (0,0091; 0,0092)`. -/
theorem par6_forcado :
    (3 / 1000 < bForcado (7987 / 1000000) (-(5 / 100000)) ∧
      bForcado (7987 / 1000000) (-(5 / 100000)) < 31 / 10000) ∧
    (58 / 10000 < bForcado (7987 / 1000000) (-(1 / 10000)) ∧
      bForcado (7987 / 1000000) (-(1 / 10000)) < 59 / 10000) ∧
    (91 / 10000 < bForcado (7987 / 1000000) (-(2 / 10000)) ∧
      bForcado (7987 / 1000000) (-(2 / 10000)) < 92 / 10000) := by
  unfold bForcado
  refine ⟨metade_raiz_entre ?_ ?_ ?_ ?_, metade_raiz_entre ?_ ?_ ?_ ?_, metade_raiz_entre ?_ ?_ ?_ ?_⟩ <;> norm_num

/-- **Os valores 0,00245 (na colisão) e 0,00678 (em `t = −10⁻⁴`) estão errados.** -/
theorem par6_valores_errados :
    bForcado (7987 / 1000000) (-((7987 / 1000000 : ℝ) ^ 2) / 2) ≠ 245 / 100000 ∧
      bForcado (7987 / 1000000) (-(1 / 10000)) < 678 / 100000 := by
  refine ⟨by rw [b_na_colisao]; norm_num, ?_⟩
  have := par6_forcado.2.1.2
  linarith

/-! ## 3. de Bruijn–Newman -/

/-- **RH ⟺ `Λ = 0`**, dados Rodgers–Tao (`Λ ≥ 0`) e de Bruijn–Newman (RH ⟺ `Λ ≤ 0`), ambos enunciados nomeados. -/
theorem rh_iff_lambda_zero (hRT : Fronteira.RodgersTao) (h : Fronteira.RH_iff_Lambda) :
    RiemannHypothesis ↔ Fronteira.deBruijnNewman = 0 :=
  h.trans ⟨fun h' => le_antisymm h' hRT, fun h' => h'.le⟩

/-- **"Λ → 0⁻" não existe**: com Rodgers–Tao, `Λ < 0` é impossível. -/
theorem lambda_negativo_impossivel (hRT : Fronteira.RodgersTao) : ¬ Fronteira.deBruijnNewman < 0 :=
  not_lt.mpr hRT

/-- **Uma cota de par de Lehmer não melhora nada**: qualquer `l < 0` (por exemplo `λ = −4,59·10⁻⁷` do par mais frágil
da continuação) fica estritamente abaixo de `Λ`, que já é `≥ 0`. -/
theorem cota_de_lehmer_mais_fraca (hRT : Fronteira.RodgersTao) {l : ℝ} (hl : l < 0) :
    l < Fronteira.deBruijnNewman :=
  lt_of_lt_of_le hl hRT

/-! ## 4. Gram com `j` zeros num intervalo -/

section Gram

variable (N₀ : ℤ) (Γ : Finset ℝ) (θ : ℝ → ℝ)

/-- **`j` zeros num intervalo de Gram fazem `S` subir `j − 1`.** -/
theorem gram_k_zeros {g₁ g₂ : ℝ} {m : ℤ} {j : ℕ} (h : g₁ ≤ g₂) (h1 : θ g₁ = m * Real.pi)
    (h2 : θ g₂ = (m + 1) * Real.pi) (hj : Leis.entre Γ g₁ g₂ = j) :
    Leis.S N₀ Γ θ g₂ = Leis.S N₀ Γ θ g₁ + ((j : ℝ) - 1) := by
  have := Leis.lei_gram N₀ Γ θ h h1 (k := 1) (by rw [h2]; push_cast; ring)
  rw [hj] at this
  push_cast at this
  linarith

/-- **Gram quádruplo** (o intervalo `[g_{12363155349036}, g_{…037})` da continuação): `S` sobe 3. -/
theorem gram_quadruplo {g₁ g₂ : ℝ} {m : ℤ} (h : g₁ ≤ g₂) (h1 : θ g₁ = m * Real.pi)
    (h2 : θ g₂ = (m + 1) * Real.pi) (h4 : Leis.entre Γ g₁ g₂ = 4) :
    Leis.S N₀ Γ θ g₂ = Leis.S N₀ Γ θ g₁ + 3 := by
  have := gram_k_zeros N₀ Γ θ h h1 h2 h4
  rw [this]
  norm_num

end Gram

/-! ## 5. A janela da continuação a partir das contagens -/

/-- Sem zero fora da reta na janela ⟹ a janela está na reta. -/
theorem janelaNaReta_de_fora_vazio {T₁ T₂ : ℝ} (h : Paridade.Fora T₁ T₂ = ∅) : Turing.JanelaNaReta T₁ T₂ := by
  intro s hs
  by_contra hne
  have hf : s ∈ Paridade.Fora T₁ T₂ := ⟨hs, hne⟩
  rw [h] at hf
  exact hf

/-- Uma janela na reta continua na reta se o topo desce. -/
theorem janelaNaReta_restringe {T₁ T₂ T₃ : ℝ} (h : Turing.JanelaNaReta T₁ T₂) (h32 : T₃ ≤ T₂) :
    Turing.JanelaNaReta T₁ T₃ :=
  fun s ⟨hz, ha, hb⟩ => h s ⟨hz, ha, hb.trans h32⟩

/-- **Uma faixa que fecha está na reta**: `N(b) − N(a) = k` e pelo menos `k` zeros achados na reta. -/
theorem faixa_na_reta {a b : ℝ} {k : ℕ} (ha : 1 ≤ a) (hN : (Paridade.NaJanela a b).ncard = k)
    (hL : k ≤ (Paridade.NaReta a b).ncard) : Turing.JanelaNaReta a b :=
  janelaNaReta_de_fora_vazio (Paridade.fecha_de_contagens ha hN hL)

/-- **As quatro faixas da continuação (execução 41559243734) colam numa janela na reta**: as hipóteses são os
números que a Arb devolveu (`N(b) − N(a)` exato e os zeros achados na reta em cada faixa). -/
theorem continuacao_de_contagens
    (h0N : (Paridade.NaJanela 3000175342471.5 3000175462471.5).ncard = 513596)
    (h0L : 513596 ≤ (Paridade.NaReta 3000175342471.5 3000175462471.5).ncard)
    (h1N : (Paridade.NaJanela 3000175462471.5 3000175582471.5).ncard = 513596)
    (h1L : 513596 ≤ (Paridade.NaReta 3000175462471.5 3000175582471.5).ncard)
    (h2N : (Paridade.NaJanela 3000175582471.5 3000175702471.5).ncard = 513595)
    (h2L : 513595 ≤ (Paridade.NaReta 3000175582471.5 3000175702471.5).ncard)
    (h3N : (Paridade.NaJanela 3000175702471.5 3000175822471.5).ncard = 513596)
    (h3L : 513596 ≤ (Paridade.NaReta 3000175702471.5 3000175822471.5).ncard) :
    Turing.JanelaNaReta 3000175342471.5 3000175822471.5 :=
  Turing.janelas_colam
    (Turing.janelas_colam
      (Turing.janelas_colam (faixa_na_reta (by norm_num) h0N h0L) (faixa_na_reta (by norm_num) h1N h1L))
      (faixa_na_reta (by norm_num) h2N h2L))
    (faixa_na_reta (by norm_num) h3N h3L)

/-- **`JanelaContinuacao2026` sai das contagens**: a fatia `(…342 471; …342 471,5]` (seção 13) mais as quatro faixas. -/
theorem janelaContinuacao_de_contagens
    (h13 : Turing.JanelaNaReta 3000175342471 3000175342471.5)
    (h0N : (Paridade.NaJanela 3000175342471.5 3000175462471.5).ncard = 513596)
    (h0L : 513596 ≤ (Paridade.NaReta 3000175342471.5 3000175462471.5).ncard)
    (h1N : (Paridade.NaJanela 3000175462471.5 3000175582471.5).ncard = 513596)
    (h1L : 513596 ≤ (Paridade.NaReta 3000175462471.5 3000175582471.5).ncard)
    (h2N : (Paridade.NaJanela 3000175582471.5 3000175702471.5).ncard = 513595)
    (h2L : 513595 ≤ (Paridade.NaReta 3000175582471.5 3000175702471.5).ncard)
    (h3N : (Paridade.NaJanela 3000175702471.5 3000175822471.5).ncard = 513596)
    (h3L : 513596 ≤ (Paridade.NaReta 3000175702471.5 3000175822471.5).ncard) :
    Continuacao.JanelaContinuacao2026 :=
  janelaNaReta_restringe
    (Turing.janelas_colam h13 (continuacao_de_contagens h0N h0L h1N h1L h2N h2L h3N h3L)) (by norm_num)

/-- **RH até `3 000 175 822 471` a partir das contagens** (com Platt–Trudgian e a janela da seção 13). -/
theorem rhAteZ_de_contagens (hPT : PlattTrudgian2021) (hJ : PrimeiroFora.JanelaArb2026)
    (h13 : Turing.JanelaNaReta 3000175342471 3000175342471.5)
    (h0N : (Paridade.NaJanela 3000175342471.5 3000175462471.5).ncard = 513596)
    (h0L : 513596 ≤ (Paridade.NaReta 3000175342471.5 3000175462471.5).ncard)
    (h1N : (Paridade.NaJanela 3000175462471.5 3000175582471.5).ncard = 513596)
    (h1L : 513596 ≤ (Paridade.NaReta 3000175462471.5 3000175582471.5).ncard)
    (h2N : (Paridade.NaJanela 3000175582471.5 3000175702471.5).ncard = 513595)
    (h2L : 513595 ≤ (Paridade.NaReta 3000175582471.5 3000175702471.5).ncard)
    (h3N : (Paridade.NaJanela 3000175702471.5 3000175822471.5).ncard = 513596)
    (h3L : 513596 ≤ (Paridade.NaReta 3000175702471.5 3000175822471.5).ncard) :
    RHateZ 3000175822471 :=
  Continuacao.rhAteZ_continuacao hPT hJ
    (janelaContinuacao_de_contagens h13 h0N h0L h1N h1L h2N h2L h3N h3L)

/-! ## 6. Não há aniquilação: na colisão o par vira um zero duplo e depois sai da reta junto

No modelo de colisão `H₂(z) = z² − a² − 2t` (a distância do par é `2a`; `Colisao.H2`), os zeros nunca somem nem se
anulam um com o outro: são sempre `±w` com `w² = a² + 2t`. Para `t > −a²/2` são reais (dois zeros na reta); em
`t = −a²/2` coincidem (zero duplo); para `t < −a²/2` são `±i r` (o par saiu da reta, em `s = ½ ∓ r/2`). -/

/-- **Os zeros do modelo são sempre o par `±w`**, com `w² = a² + 2t`. -/
theorem h2_fatora (a t : ℝ) {w : ℂ} (hw : w ^ 2 = (a : ℂ) ^ 2 + 2 * (t : ℂ)) (z : ℂ) :
    Colisao.H2 a t z = (z - w) * (z + w) := by
  unfold Colisao.H2
  linear_combination hw

/-- **Os zeros nunca somem**: para todo `t` há `w` com `H₂(w) = H₂(−w) = 0`. -/
theorem zeros_nunca_somem (a t : ℝ) : ∃ w : ℂ, Colisao.H2 a t w = 0 ∧ Colisao.H2 a t (-w) = 0 := by
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w ^ 2 = (a : ℂ) ^ 2 + 2 * (t : ℂ) :=
    ⟨_, Complex.cpow_nat_inv_pow _ two_ne_zero⟩
  exact ⟨w, by rw [h2_fatora a t hw]; ring, by rw [h2_fatora a t hw]; ring⟩

/-- **Na colisão (`t = −a²/2`) os dois zeros coincidem**: `H₂(z) = z²`, um zero duplo em `z = 0`. -/
theorem colisao_zero_duplo (a : ℝ) (z : ℂ) : Colisao.H2 a (-(a ^ 2) / 2) z = z ^ 2 := by
  unfold Colisao.H2
  push_cast
  ring

/-- **Depois da colisão o par sai da reta junto**, em `z = ±i r` com `r = √(2(−a²/2 − t)) > 0`. -/
theorem depois_da_colisao (a t : ℝ) (ht : t < -(a ^ 2) / 2) :
    ∃ r : ℝ, 0 < r ∧ Colisao.H2 a t (I * r) = 0 ∧ Colisao.H2 a t (-(I * r)) = 0 := by
  have h1 := (Colisao.raiz_quadrada a t ht.le).1
  refine ⟨Real.sqrt (2 * (-(a ^ 2) / 2 - t)), Real.sqrt_pos.mpr (by linarith), h1, ?_⟩
  have e : Colisao.H2 a t (-(I * (Real.sqrt (2 * (-(a ^ 2) / 2 - t)) : ℂ))) =
      Colisao.H2 a t (I * (Real.sqrt (2 * (-(a ^ 2) / 2 - t)) : ℂ)) := by
    unfold Colisao.H2
    ring
  rw [e, h1]

end ClayRiemannProof.Correcoes
