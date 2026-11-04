import ClayRiemannProof.Biblioteca.Entradas
import ClayRiemannProof.Continuacao

/-!
# RH reduzida: o que sobra depois das simetrias, da altura 13 e da verificação

Cada passo abaixo é uma **equivalência provada** (RH ⟺ uma afirmação sobre uma região menor). Nenhum passo é RH: o
que sobra continua aberto.

1. **Um lado** (`rh_de_metade`, `Entradas`): basta excluir zeros com `Re s > ½`; a reflexão `s ↦ 1 − s̄` da equação
   funcional dá o outro lado.
2. **Um quarto** (`rh_iff_acima`): basta excluir zeros com `Re s > ½` e `Im s > T`, desde que RH valha até a altura
   `T`; o espelho `s ↦ s̄` (`ζ(s̄) = conj ζ(s)`, Mathlib) leva a metade de baixo para a de cima.
3. **Incondicional a partir de 13** (`rh_iff_quarto`): não há zeros com `|Im s| ≤ 13` na faixa
   (`HeightThirteen.faixa_sem_zeros`), então RH ⟺ nenhum zero com `Re s > ½` e `Im s > 13`.
4. **Com a verificação certificada** (`rh_reduzida`, `Resto`): com Platt–Trudgian e as seis janelas da Arb como
   hipóteses nomeadas, RH ⟺ nenhum zero com `Re s > ½` e `Im s > 3 000 181 942 471`.
5. **Em caixas** (`rh_iff_caixas`): RH ⟺ cada caixa `[T + n·w, T + (n + 1)·w)` não tem zero com `Re s > ½`. Cada
   caixa é uma verificação finita (é o que uma faixa da continuação faz com `w = 120 000`); RH é a conjunção de todas.
6. **Com a região livre clássica** (`rh_iff_faixa_estreita`): com a região de de la Vallée Poussin como hipótese
   nomeada (`RegiaoLivreClassica c`; Mossinghoff–Trudgian–Yang dão `c = 1/5,558691` para `Im s ≥ 2`), sobra só a faixa
   `½ < Re s < 1 − c/log(Im s)`.

`OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Biblioteca

open Complex ClayRiemannProof.Zeta.Symmetry

/-- RH no conjunto `Z` dos zeros da faixa. -/
theorem rh_iff_re_Z : RiemannHypothesis ↔ ∀ s ∈ Z, s.re = 1 / 2 := by
  rw [riemann_iff_torcao]
  exact forall₂_congr fun s _ => torcao_fixo_iff s

/-- **Um quarto basta, acima de qualquer altura onde RH já vale.** -/
theorem rh_iff_acima {T : ℝ} (hT : ∀ s ∈ Z, |s.im| ≤ T → s.re = 1 / 2) :
    RiemannHypothesis ↔ ∀ s ∈ Z, T < s.im → s.re ≤ 1 / 2 := by
  rw [rh_iff_re_Z]
  constructor
  · intro h s hs _
    exact (h s hs).le
  · intro h s hs
    by_cases hle : |s.im| ≤ T
    · exact hT s hs hle
    · push_neg at hle
      rcases lt_abs.mp hle with hp | hn
      · have h1 := h s hs hp
        have h2 := h (torcao s) (torcao_mem_Z hs) (by simpa [torcao] using hp)
        have h3 : (torcao s).re = 1 - s.re := by simp [torcao]
        linarith
      · have h1 := h (espelho s) (espelho_mem_Z hs) (by simp [espelho]; linarith)
        have h2 := h (tensao s) (tensao_mem_Z hs) (by simp [tensao]; linarith)
        have h3 : (espelho s).re = s.re := by simp [espelho]
        have h4 : (tensao s).re = 1 - s.re := by simp [tensao]
        linarith

/-- **Incondicional**: RH ⟺ nenhum zero com `Re s > ½` e `Im s > 13`. -/
theorem rh_iff_quarto : RiemannHypothesis ↔ ∀ s ∈ Z, 13 < s.im → s.re ≤ 1 / 2 :=
  rh_iff_acima fun s hs h => absurd hs.1 (HeightThirteen.faixa_sem_zeros hs.2.1 hs.2.2 h)

/-- RH até a altura `N` (no enunciado do Mathlib) vale para os zeros de `Z` com `|Im s| ≤ N`. -/
theorem re_de_rhateZ {N : ℕ} (h : FiniteWorlds.RHateZ N) : ∀ s ∈ Z, |s.im| ≤ N → s.re = 1 / 2 := by
  intro s hs him
  obtain ⟨hz, h0, h1⟩ := hs
  refine h s hz ?_ ?_ him
  · rintro ⟨n, rfl⟩
    have hre : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by simp
    rw [hre] at h0
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  · rintro rfl
    simp at h1

/-- **O que sobra de RH** depois da verificação certificada: nenhum zero não trivial com `Re s > ½` e
`Im s > 3 000 181 942 471`. -/
def Resto : Prop := ∀ s ∈ Z, ((3000181942471 : ℕ) : ℝ) < s.im → s.re ≤ 1 / 2

/-- **RH reduzida ao resto**, com Platt–Trudgian e as seis janelas da Arb como hipóteses nomeadas. -/
theorem rh_reduzida (hPT : FiniteWorlds.PlattTrudgian2021) (hJ : PrimeiroFora.JanelaArb2026)
    (hC : Continuacao.JanelaContinuacao2026) (hC2 : Continuacao.JanelaContinuacao2026b)
    (hC3 : Continuacao.JanelaContinuacao2026c) (hC4 : Continuacao.JanelaContinuacao2026d)
    (hC5 : Continuacao.JanelaContinuacao2026e) : RiemannHypothesis ↔ Resto :=
  rh_iff_acima (re_de_rhateZ (Continuacao.rhAteZ_continuacao5 hPT hJ hC hC2 hC3 hC4 hC5))

/-- **Caixa livre**: nenhum zero com `Re s > ½` e `a ≤ Im s < a + w`. -/
def CaixaLivre (a w : ℝ) : Prop := ∀ s ∈ Z, a ≤ s.im → s.im < a + w → s.re ≤ 1 / 2

/-- **RH em caixas**: acima de uma altura `T ≥ 0` onde RH já vale, RH ⟺ toda caixa de largura `w` está livre. -/
theorem rh_iff_caixas {T w : ℝ} (hT0 : 0 ≤ T) (hw : 0 < w) (hT : ∀ s ∈ Z, |s.im| ≤ T → s.re = 1 / 2) :
    RiemannHypothesis ↔ ∀ n : ℕ, CaixaLivre (T + n * w) w := by
  rw [rh_iff_acima hT]
  constructor
  · intro h n s hs ha _
    by_cases hTs : T < s.im
    · exact h s hs hTs
    · push_neg at hTs
      have hn : (0 : ℝ) ≤ n * w := mul_nonneg (Nat.cast_nonneg n) hw.le
      have heq : s.im = T := le_antisymm hTs (by linarith)
      have habs : |s.im| ≤ T := by rw [heq, abs_of_nonneg hT0]
      exact (hT s hs habs).le
  · intro h s hs hTs
    have hw0 : w ≠ 0 := hw.ne'
    set x := (s.im - T) / w with hxdef
    have hx : 0 ≤ x := div_nonneg (by linarith) hw.le
    have hxw : x * w = s.im - T := by rw [hxdef]; field_simp
    have h1 : (⌊x⌋₊ : ℝ) * w ≤ x * w := mul_le_mul_of_nonneg_right (Nat.floor_le hx) hw.le
    have h2 : x * w < ((⌊x⌋₊ : ℝ) + 1) * w := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one x) hw
    exact h ⌊x⌋₊ s hs (by linarith) (by linarith)

/-- **Região livre clássica** (de la Vallée Poussin), como hipótese nomeada: o Mathlib só tem `Re s ≥ 1`.
Mossinghoff, Trudgian e Yang provaram a forma com `c = 1/5,558691`. -/
def RegiaoLivreClassica (c : ℝ) : Prop := ∀ s ∈ Z, 2 ≤ s.im → s.re < 1 - c / Real.log s.im

/-- **Com a região livre clássica, sobra uma faixa estreita**: RH ⟺ nenhum zero com
`½ < Re s < 1 − c/log(Im s)` e `Im s > T`. -/
theorem rh_iff_faixa_estreita {T c : ℝ} (hT2 : 2 ≤ T) (hR : RegiaoLivreClassica c)
    (hT : ∀ s ∈ Z, |s.im| ≤ T → s.re = 1 / 2) :
    RiemannHypothesis ↔ ∀ s ∈ Z, T < s.im → s.re < 1 - c / Real.log s.im → s.re ≤ 1 / 2 := by
  rw [rh_iff_acima hT]
  constructor
  · intro h s hs hTs _
    exact h s hs hTs
  · intro h s hs hTs
    exact h s hs hTs (hR s hs (by linarith))

end ClayRiemannProof.Biblioteca
