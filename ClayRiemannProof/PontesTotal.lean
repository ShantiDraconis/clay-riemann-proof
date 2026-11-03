import ClayRiemannProof.Bridges
import ClayRiemannProof.LiCircle
import ClayRiemannProof.CenteredStabilityBridge

/-!
# Todas as pontes: as 22 formulações do repositório são a mesma proposição

`Bridges.pontes` reuniu 13 formulações e `LiCircle.encontro` reuniu 5. Este arquivo junta **toda** equivalência com o
enunciado do Clay que existe no repositório num único `List.TFAE`. Entram:
- Báez-Duarte nas duas formas: `⨅ D_N = 0` e `D_N → 0`;
- o corte em `ω`, os mundos finitos e o bicomplexo;
- o desvio `b = 0` e o semiplano direito;
- os fins e os inícios fechados;
- a torção, a compressão e os colares;
- a energia, os nós, `λ` real e `γ` real;
- a coordenada centrada (branch `bicomplex-coordinate-algebra`);
- `ξ`, o círculo, Li por quartetos e Ramanujan.

**O que isto não é**: provar qualquer uma das 22 é provar RH, e nenhuma é mais fraca que as outras. Nada aqui
prova RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.PontesTotal

open Filter Topology Complex ClayRiemannProof.Zeta.Symmetry ClayRiemannProof.Bridges
  ClayRiemannProof.LiCircle

/-- **A ponte total**: as 22 formulações do repositório são equivalentes ao enunciado do Clay.

 1. Clay; 2. `⨅ D_N = 0`; 3. `D_N → 0`; 4. `D_ω` infinitesimal; 5. todo mundo finito; 6. RH bicomplexa;
 7. desvio `b = 0`; 8. sem zeros em `½ < Re s < 1`; 9. fins fechados livres; 10. inícios fechados livres;
11. torção fixa os zeros; 12. compressão preserva `Re`; 13. colares arbitrariamente finos; 14. energia zero;
15. nós desfeitos; 16. `λ` real; 17. `γ` real; 18. coordenada centrada neutra; 19. zeros de `ξ` na reta;
20. `1 − 1/ρ` no círculo; 21. Li por quartetos; 22. Ramanujan. -/
theorem pontes_total : List.TFAE
    [ Target,
      Gap,
      Tendsto ClayRiemannProof.BaezDuarte.DN atTop (𝓝 0),
      HyperTruncation.IsInfinitesimal HyperTruncation.DOmega,
      ∀ M : ℕ, FiniteWorlds.RHnoMundo M,
      Bicomplex.RHbc,
      ∀ ρ : ℂ, riemannZeta ρ = 0 → (¬ ∃ n : ℕ, ρ = -2 * (n + 1)) → ρ ≠ 1 → ρ.re - 1 / 2 = 0,
      NoZero_right_half,
      ∀ a : ℝ, 1 / 2 < a → FimLivre a,
      ∀ b : ℝ, b < 1 / 2 → InicioLivre b,
      ∀ s ∈ Z, torcao s = s,
      ∀ s ∈ Z, ∀ l : ℝ, (compressao l s).re = s.re,
      ∀ ε : ℝ, 0 < ε → ∀ s ∈ Z, |s.re - 1 / 2| < ε,
      ∀ s ∈ Z, energia s = 0,
      ∀ s ∈ Z, (orbita s).card = 2,
      ∀ s ∈ Z, (lam s).im = 0,
      ∀ s ∈ Z, (gam s).im = 0,
      ∀ s ∈ Z, (CenteredStabilityBridge.centered s).re = 0,
      ∀ s : ℂ, ClayRiemannProof.Xi.xi s = 0 → s.re = 1 / 2,
      ∀ ρ ∈ Z, normSq (mob ρ) = 1,
      ∀ ρ ∈ Z, ∀ n : ℕ, 0 ≤ liQ (mob ρ) n,
      ∀ ρ ∈ Z, ∃ c : ℝ, c ^ 2 ≤ 4 ∧ 1 - (c : ℂ) * mob ρ + ((1 : ℝ) : ℂ) * mob ρ ^ 2 = 0 ] := by
  have hp := pontes
  tfae_have 1 ↔ 2 := target_iff_gap
  tfae_have 1 ↔ 3 := ClayRiemannProof.BaezDuarte.Necessity.rh_iff_DN
  tfae_have 1 ↔ 4 := HyperTruncation.target_iff_DOmega_infinitesimal
  tfae_have 1 ↔ 5 := FiniteWorlds.target_iff_todos_os_mundos
  tfae_have 1 ↔ 6 := Bicomplex.target_iff_RHbc
  tfae_have 1 ↔ 7 := Locks.target_iff_desvio_zero
  tfae_have 1 ↔ 8 := target_iff_noZero_right_half
  tfae_have 1 ↔ 9 := riemann_iff_fim
  tfae_have 1 ↔ 10 := riemann_iff_inicio
  tfae_have 1 ↔ 11 := riemann_iff_torcao
  tfae_have 1 ↔ 12 := riemann_iff_compressao
  tfae_have 1 ↔ 13 := riemann_iff_colares
  tfae_have 1 ↔ 14 := hp.out 1 10
  tfae_have 1 ↔ 15 := target_iff_nos_desfeitos
  tfae_have 1 ↔ 16 := target_iff_lam_real
  tfae_have 1 ↔ 17 := target_iff_gam_real
  tfae_have 1 ↔ 18 := CenteredStabilityBridge.riemann_iff_centered_neutral
  tfae_have 1 ↔ 19 := ClayRiemannProof.Xi.target_iff_xi
  tfae_have 1 ↔ 20 := target_iff_circulo
  tfae_have 1 ↔ 21 := target_iff_li_quartetos
  tfae_have 1 ↔ 22 := target_iff_ramanujan
  tfae_finish

end ClayRiemannProof.PontesTotal
