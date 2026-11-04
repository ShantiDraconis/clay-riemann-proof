import ClayRiemannProof.Biblioteca.HilbertPolya
import ClayRiemannProof.Biblioteca.Euler
import ClayRiemannProof.PontesTotal
import ClayRiemannProof.Fronteira.Clay
import ClayRiemannProof.Correcoes

/-!
# As entradas abertas de RH e as pontes já provadas

Cada rota abaixo tem uma **entrada aberta** (uma proposição que ninguém provou) e uma **ponte** (o teorema, provado
no kernel, que leva da entrada a RH). Provar qualquer entrada fecha RH aqui, sem mais trabalho formal:

| rota | entrada aberta | ponte |
|---|---|---|
| espectral (Hilbert–Pólya) | `HilbertPolya` | `rh_de_hilbertPolya` |
| fluxo do calor (de Bruijn–Newman) | `deBruijnNewman ≤ 0`, com o teorema clássico `RH_iff_Lambda` como hipótese nomeada | `rotas_para_rh` |
| Li | `PositividadeDeLi`, com `CriterioDeLi` como hipótese nomeada | `rotas_para_rh` |
| um lado só | nenhum zero com `Re s > ½` | `rh_de_metade` (a equação funcional dá o outro lado) |
| Báez-Duarte / Nyman–Beurling | `D_N → 0` | `BaezDuarte.Necessity.rh_iff_DN` (equivalência provada, sem hipótese) |
| verificação | RH até a altura `Z` para **todo** `Z` | `FiniteWorlds.target_iff_todos_os_mundos` (equivalência provada) |

O que **não** é entrada: uma cota `λ < 0` de par de Lehmer (é mais fraca que `Λ ≥ 0`,
`Correcoes.cota_de_lehmer_mais_fraca`); uma média ½ de qualquer reparametrização (`Absorcao.media_reAbs`, vale para
qualquer lista); o produto de Euler em `σ = ½` (diverge, `Biblioteca.fronteiras_de_euler`); qualquer altura finita
(`FiniteWorlds.not_target_iff_um_mundo`: RH falsa é um contraexemplo numa altura finita, mas RH verdadeira não é
nenhuma altura finita). `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Biblioteca

open Filter Topology Complex ClayRiemannProof.Zeta.Symmetry

/-- **Metade basta**: se nenhum zero não trivial tem `Re s > ½`, vale RH. A equação funcional (pela reflexão
`s ↦ 1 − s̄`, `Zeta.Symmetry.torcao_mem_Z`) leva qualquer zero com `Re s < ½` a um com `Re s > ½`. -/
theorem rh_de_metade (h : ∀ s ∈ Z, s.re ≤ 1 / 2) : RiemannHypothesis := by
  rw [riemann_iff_torcao]
  intro s hs
  rw [torcao_fixo_iff]
  have h1 := h s hs
  have h2 := h (torcao s) (torcao_mem_Z hs)
  have h3 : (torcao s).re = 1 - s.re := by simp [torcao]
  linarith

/-- **As pontes das rotas com entrada aberta**. -/
theorem rotas_para_rh :
    (HilbertPolya → RiemannHypothesis) ∧
    (Fronteira.RH_iff_Lambda → Fronteira.deBruijnNewman ≤ 0 → RiemannHypothesis) ∧
    (Fronteira.CriterioDeLi → Fronteira.PositividadeDeLi → RiemannHypothesis) ∧
    ((∀ s ∈ Z, s.re ≤ 1 / 2) → RiemannHypothesis) :=
  ⟨rh_de_hilbertPolya, fun h hΛ => h.mpr hΛ, fun h hp => h.mpr hp, rh_de_metade⟩

/-- **As equivalências provadas sem nenhuma hipótese** (escolhidas da ponte total de 22 formulações,
`PontesTotal.pontes_total`). -/
theorem equivalencias_sem_hipotese :
    (RiemannHypothesis ↔ Tendsto BaezDuarte.DN atTop (𝓝 0)) ∧
    (RiemannHypothesis ↔ ∀ s ∈ Z, s.re ≤ 1 / 2) ∧
    (RiemannHypothesis ↔ ∀ s ∈ Z, torcao s = s) :=
  ⟨BaezDuarte.Necessity.rh_iff_DN, ⟨fun h s hs => (riemann_imp_re h hs).le, rh_de_metade⟩, riemann_iff_torcao⟩

/-- **A verificação finita**: RH é RH em toda altura finita; nenhuma altura finita basta sozinha. -/
theorem verificacao :
    (Target ↔ ∀ Z : ℕ, FiniteWorlds.RHnoMundo Z) ∧ (¬ Target ↔ ∃ Z : ℕ, ¬ FiniteWorlds.RHnoMundo Z) :=
  ⟨FiniteWorlds.target_iff_todos_os_mundos, FiniteWorlds.not_target_iff_um_mundo⟩

/-- **de Bruijn–Newman com Rodgers–Tao**: as duas hipóteses nomeadas clássicas deixam RH equivalente a `Λ = 0`, e
`Λ < 0` é impossível. -/
theorem lambda_com_rodgers_tao (hRT : Fronteira.RodgersTao) (h : Fronteira.RH_iff_Lambda) :
    (RiemannHypothesis ↔ Fronteira.deBruijnNewman = 0) ∧ ¬ Fronteira.deBruijnNewman < 0 :=
  ⟨Correcoes.rh_iff_lambda_zero hRT h, Correcoes.lambda_negativo_impossivel hRT⟩

end ClayRiemannProof.Biblioteca
