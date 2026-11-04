import ClayRiemannProof.Biblioteca.Reducao
import ClayRiemannProof.Biblioteca.Lagarias
import ClayRiemannProof.Biblioteca.Refutacao

/-!
# Reduzir o infinito: até onde dá

O que sobrou de RH (`Biblioteca.Reducao`) é um quarto de faixa infinito. O infinito não some, mas muda de tipo:

1. **Do contínuo ao enumerável** (`rh_iff_caixas`): todos os pontos da região viram uma sequência de caixas
   `n = 0, 1, 2, …`, cada uma uma verificação finita.
2. **Do analítico ao aritmético** (`Biblioteca.Lagarias`): com o critério de Lagarias, uma sequência de desigualdades
   entre inteiros e racionais; um contraexemplo seria um único inteiro (`nao_rh_iff_inteiro`).
3. **O contraexemplo é finito, a prova não** (`contraexemplo_finito`): RH falsa ⟺ falha numa altura finita; RH
   verdadeira não é nenhuma altura finita.
4. **O corte finito existe só classicamente** (`corte_em_altura`, `Lagarias.corte_existe`): existe uma altura `Z` tal
   que conferir até `Z` bastaria, mas a prova não diz qual — se RH vale, qualquer uma serve; se não vale, é a do
   contraexemplo. Um `Z` explícito com prova seria uma prova de RH.

Abaixo disso não há redução: trocar "para todo `n`" por um número finito de casos exige um teorema que limite onde um
contraexemplo poderia estar, e esse teorema é do mesmo tamanho que RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Biblioteca

/-- **O contraexemplo é finito**: RH falsa ⟺ RH falha num mundo finito (numa altura finita). -/
theorem contraexemplo_finito : ¬ Target ↔ ∃ Z : ℕ, ¬ FiniteWorlds.RHnoMundo Z :=
  FiniteWorlds.not_target_iff_um_mundo

/-- **O corte em altura existe, mas só classicamente**: há `Z` tal que RH no mundo `Sat Z` bastaria. -/
theorem corte_em_altura : ∃ Z : ℕ, FiniteWorlds.RHnoMundo Z → Target := by
  by_cases h : Target
  · exact ⟨0, fun _ => h⟩
  · obtain ⟨Z, hZ⟩ := contraexemplo_finito.mp h
    exact ⟨Z, fun h' => absurd h' hZ⟩

/-- **As três formas do infinito** num só enunciado: caixas enumeráveis acima de 13, desigualdades de Lagarias
(com o critério nomeado) e mundos finitos. -/
theorem formas_do_infinito (hL : CriterioDeLagarias) :
    (RiemannHypothesis ↔ ∀ n : ℕ, CaixaLivre (13 + n * 120000) 120000) ∧
    (RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → Lagarias n) ∧
    (Target ↔ ∀ Z : ℕ, FiniteWorlds.RHnoMundo Z) :=
  ⟨rh_iff_caixas (by norm_num) (by norm_num)
      (fun s hs h => absurd hs.1 (HeightThirteen.faixa_sem_zeros hs.2.1 hs.2.2 h)),
    hL, FiniteWorlds.target_iff_todos_os_mundos⟩

/-- **A refutação pela densidade**: RH falsa ⟺ existem `σ > ½` e `T` com `N(σ, T) ≥ 1`, isto é, um zero com
`Re s ≥ σ` e `0 < Im s ≤ T`. Uma cota superior para `N(σ, T)` não refuta nada; refutar é exibir um. -/
theorem nao_rh_iff_densidade :
    ¬ RiemannHypothesis ↔
      ∃ σ : ℝ, 1 / 2 < σ ∧ ∃ T : ℝ, ∃ s ∈ Zeta.Symmetry.Z, σ ≤ s.re ∧ 0 < s.im ∧ s.im ≤ T := by
  rw [rh_iff_quarto]
  constructor
  · intro h
    push_neg at h
    obtain ⟨s, hs, him, hre⟩ := h
    exact ⟨s.re, hre, s.im, s, hs, le_rfl, by linarith, le_rfl⟩
  · rintro ⟨σ, hσ, T, s, hs, hσs, him, _⟩ hall
    by_cases h13 : 13 < s.im
    · have := hall s hs h13
      linarith
    · push_neg at h13
      exact absurd hs.1 (HeightThirteen.faixa_sem_zeros hs.2.1 hs.2.2 (by rw [abs_of_pos him]; exact h13))

end ClayRiemannProof.Biblioteca
