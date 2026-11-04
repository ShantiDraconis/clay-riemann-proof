import ClayRiemannProof.CertifiedZeros.Pieces1
import ClayRiemannProof.CertifiedZeros.Pieces2
import ClayRiemannProof.CertifiedZeros.Pieces3
import ClayRiemannProof.LowStrip.Disc
import ClayRiemannProof.FiniteWorlds
import ClayRiemannProof.CertifiedZeros.FirstZero

/-!
# Nenhum zero de `ζ` na faixa crítica até a altura 13; o mundo finito `Z = 13`

* `faixa_ate_13`: `|ζ(s)| ≥ 1/50` em `[½, 1] × [43/50, 13]` — 50 retângulos (`CertifiedZeros/Pieces1`–`3`), cada
  um certificado por `peca_ret`: cota grosseira na região de Cauchy, `‖ζ′‖ ≤ B/r`, e uma malha de centros em que
  o retângulo certificado de `ζ(σ + it)` (`σ` racional, `mem_zetaIG`) tem norma `≥ (B/r)h + 1/50`. Ao todo
  930 avaliações certificadas, todas verificadas pelo kernel (`decide +kernel`, sem `native_decide`);
* `cota_metade`, `sem_zeros_pos`: pela torção `s ↦ 1 − s̄`, também a metade `0 < Re s < ½`;
* **`faixa_sem_zeros`: `ζ(s) ≠ 0` para `0 < Re s < 1` e `|Im s| ≤ 13`** (a faixa baixa `(Im s)² < ¾` vem de
  `ClayRiemannProof.LowStrip.Disc.zeta_ne_zero_baixo`; `Im s < 0` pela conjugação);
* **`zeros_acima_13`**: todo zero não trivial (no sentido do enunciado da Mathlib) tem `|Im s| > 13`;
* **`rhNoMundo_13`**: o mundo finito `Z = 13` de `ClayRiemannProof.FiniteWorlds` está certificado —
  vacuamente: não há zero não trivial com `|Im s| ≤ 13`;
* **`primeiro_zero_entre`**, **`altura_do_primeiro_zero`**: com o zero certificado de
  `ClayRiemannProof.CertifiedZeros.FirstZero` (contração + `decide +kernel`), existe um zero não trivial `ρ₁`
  **na reta**, simples, com `13 < Im ρ₁ ≤ 14,1347261417`, e nenhum zero tem `|Im s| ≤ 13`: a altura do zero mais
  baixo está em `(13; 14,1347261417]`, tudo no kernel.

**O que isto não é**: não é RH nem prova de RH. É um caso finito (`RHnoMundo 13`); o enunciado do Clay é
`∀ Z, RHnoMundo Z` (`FiniteWorlds.target_iff_todos_os_mundos`), e a passagem de cada `Z` para todo `Z` é o
problema em aberto. `OPEN_MATH = true`.

Origem: ATK kernel (espelho público, M-Core `390e378`), `ATK/ZeroClasses/Faixa.lean` (`faixa_ate_13`,
`cota_metade`, `im_torcao`, `sem_zeros_pos`, `faixa_sem_zeros`, `primeiro_zero_entre`), portado para Mathlib
`8fe7ce4`, nomes `ATK.ZeroClasses.Faixa.*` → `ClayRiemannProof.HeightThirteen.*`, `ATK.ZetaSimetria` →
`ClayRiemannProof.Zeta.Symmetry`, `ATK.ZetaRetangulo` → `ClayRiemannProof.LowStrip.Disc`. `zeros_acima_13`
foi reescrito com a forma do enunciado da Mathlib (no ATK: `∀ ρ ∈ Z, 13 < |ρ.im|`); `rhNoMundo_13` e
`altura_do_primeiro_zero` são novos, e `primeiro_zero_entre` ganhou a simplicidade (`ζ′(ρ₁) ≠ 0`). Não
portados, por dependerem de arquivos fora do fecho mínimo (`ATK/ZeroClasses/Escalas.lean`,
`ATK/ZeroClasses/Regions.lean`): `verificado_13`, `m_pos_ate_13`, `novo_primeiro_ponto_14`. Os axiomas estão
fixados em `ClayRiemannProof/AuditThirteen.lean`.
-/

open Complex ComplexConjugate Set

namespace ClayRiemannProof.HeightThirteen

open ClayRiemannProof.CertifiedZeros.Rectangle ClayRiemannProof.CertifiedZeros.Pieces1
  ClayRiemannProof.CertifiedZeros.Pieces2 ClayRiemannProof.CertifiedZeros.Pieces3
  ClayRiemannProof.Zeta.Symmetry

/-- **`|ζ| ≥ 1/50` em `[½, 1] × [43/50, 13]`.** -/
theorem faixa_ate_13 : ∀ z ∈ ret ((1 / 2 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ((43 / 50 : ℚ) : ℝ) ((13 : ℚ) : ℝ), ((1 / 50 : ℚ) : ℝ) ≤ ‖riemannZeta z‖ :=
  ret_split_im (tm := ((2 : ℚ) : ℝ)) faixa_0 (ret_split_im (tm := ((3 : ℚ) : ℝ)) faixa_1 (ret_split_im (tm := ((4 : ℚ) : ℝ)) faixa_2 (ret_split_im (tm := ((5 : ℚ) : ℝ)) faixa_3 (ret_split_im (tm := ((6 : ℚ) : ℝ)) faixa_4 (ret_split_im (tm := ((7 : ℚ) : ℝ)) faixa_5 (ret_split_im (tm := ((8 : ℚ) : ℝ)) faixa_6 (ret_split_im (tm := ((9 : ℚ) : ℝ)) faixa_7 (ret_split_im (tm := ((10 : ℚ) : ℝ)) faixa_8 (ret_split_im (tm := ((11 : ℚ) : ℝ)) faixa_9 (ret_split_im (tm := ((12 : ℚ) : ℝ)) faixa_10 (faixa_11)))))))))))

theorem cota_metade {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 1) (h3 : 43 / 50 ≤ s.im) (h4 : s.im ≤ 13) :
    (1 / 50 : ℝ) ≤ ‖riemannZeta s‖ := by
  have := faixa_ate_13 s ⟨by push_cast; linarith, by push_cast; linarith, by push_cast; linarith,
    by push_cast; linarith⟩
  push_cast at this
  exact this

theorem im_torcao (s : ℂ) : (torcao s).im = s.im := by
  unfold torcao
  simp

theorem sem_zeros_pos {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (h3 : 43 / 50 ≤ s.im) (h4 : s.im ≤ 13) :
    riemannZeta s ≠ 0 := by
  intro hz
  rcases le_or_gt (1 / 2) s.re with hr | hr
  · have := cota_metade hr h1.le h3 h4
    rw [hz, norm_zero] at this
    norm_num at this
  · have hT := torcao_mem_Z (⟨hz, h0, h1⟩ : s ∈ Z)
    have e := re_torcao s
    have := cota_metade (s := torcao s) (by rw [e]; linarith) (by rw [e]; linarith)
      (by rw [im_torcao]; exact h3) (by rw [im_torcao]; exact h4)
    rw [hT.1, norm_zero] at this
    norm_num at this

/-- **Não há zero de `ζ` na faixa crítica com `|Im s| ≤ 13`.** -/
theorem faixa_sem_zeros {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (ht : |s.im| ≤ 13) :
    riemannZeta s ≠ 0 := by
  by_cases hb : s.im ^ 2 < 3 / 4
  · exact ClayRiemannProof.LowStrip.Disc.zeta_ne_zero_baixo h0 h1 hb
  have hb' : 43 / 50 ≤ |s.im| := by
    by_contra hc
    have hc' : |s.im| < 43 / 50 := lt_of_not_ge hc
    have h2 : |s.im| ^ 2 < (43 / 50) ^ 2 := pow_lt_pow_left₀ hc' (abs_nonneg _) (by norm_num)
    rw [sq_abs] at h2
    exact hb (by linarith)
  rcases le_or_gt 0 s.im with hi | hi
  · rw [abs_of_nonneg hi] at hb' ht
    exact sem_zeros_pos h0 h1 hb' ht
  · rw [abs_of_neg hi] at hb' ht
    intro hz
    have hc : riemannZeta (conj s) = 0 := by rw [riemannZeta_conj, hz, map_zero]
    exact sem_zeros_pos (s := conj s) (by simpa using h0) (by simpa using h1) (by simpa using hb')
      (by simpa using ht) hc

/-- **Todo zero não trivial tem `|Im s| > 13`** (zero não trivial no sentido do enunciado da Mathlib:
`ζ(s) = 0`, `s` não é `−2(n+1)` e `s ≠ 1`). -/
theorem zeros_acima_13 : ∀ s : ℂ, riemannZeta s = 0 → (¬ ∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
    13 < |s.im| := by
  intro s hz ht _
  by_contra h
  have h13 : |s.im| ≤ 13 := le_of_not_gt h
  by_cases hle : s.re ≤ 0
  · exact ht (zero_trivial_de_re_nao_pos hz hle)
  by_cases hge : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hge hz
  exact faixa_sem_zeros (by linarith) (by linarith) h13 hz

/-- **O mundo finito `Z = 13` está certificado**: `RHnoMundo 13`, isto é, todo zero não trivial com
`|Im s| ≤ 13` está na reta `Re s = 1/2` — **vacuamente**, porque não há zero não trivial nessa altura
(`zeros_acima_13`). Isto **não** é RH: é um único mundo finito; RH é `∀ Z, RHnoMundo Z`
(`FiniteWorlds.target_iff_todos_os_mundos`). -/
theorem rhNoMundo_13 : ClayRiemannProof.FiniteWorlds.RHnoMundo 13 := by
  rw [ClayRiemannProof.FiniteWorlds.rhNoMundo_iff]
  intro s hz ht hs1 him
  have him' : |s.im| ≤ 13 := by exact_mod_cast him
  exact absurd him' (not_le.mpr (zeros_acima_13 s hz ht hs1))

/-- **O primeiro zero**: existe `ρ₁` não trivial na reta, a menos de `10⁻⁶` de `½ + 14,1347251417 i` e simples
(`FirstZero.zero_simples`, certificado pelo kernel), e todo zero não trivial tem `|Im ρ| > 13`. -/
theorem primeiro_zero_entre :
    (∃ ρ ∈ Z, ρ.re = 1 / 2 ∧
        ρ ∈ Metric.closedBall ClayRiemannProof.CertifiedZeros.FirstZero.z0
          ((ClayRiemannProof.CertifiedZeros.FirstZero.rr : ℚ) : ℝ) ∧ deriv riemannZeta ρ ≠ 0) ∧
      ∀ ρ ∈ Z, 13 < |ρ.im| := by
  refine ⟨ClayRiemannProof.CertifiedZeros.FirstZero.zero_simples, fun ρ hρ => ?_⟩
  by_contra h
  exact faixa_sem_zeros hρ.2.1 hρ.2.2 (le_of_not_gt h) hρ.1

/-- **A altura do zero mais baixo está em `(13; 14,1347261417]`**: há um zero não trivial `ρ₁` na reta com
`13 < Im ρ₁ ≤ 14,1347261417`, e nenhum zero não trivial tem `|Im ρ| ≤ 13`. -/
theorem altura_do_primeiro_zero :
    (∃ ρ ∈ Z, ρ.re = 1 / 2 ∧ 13 < ρ.im ∧ ρ.im ≤ 141347261417 / 10 ^ 10) ∧ ∀ ρ ∈ Z, 13 < |ρ.im| := by
  obtain ⟨⟨ρ, hρ, hre, hB, -⟩, h13⟩ := primeiro_zero_entre
  have him := (ClayRiemannProof.CertifiedZeros.FirstZero.re_im_prox hB).2
  rw [ClayRiemannProof.CertifiedZeros.FirstZero.t0_val, abs_le] at him
  have hr : ((ClayRiemannProof.CertifiedZeros.FirstZero.rr : ℚ) : ℝ) = 1 / 10 ^ 6 := by
    simp [ClayRiemannProof.CertifiedZeros.FirstZero.rr]
  rw [hr] at him
  exact ⟨⟨ρ, hρ, hre, by linarith [him.1], by linarith [him.2]⟩, h13⟩

end ClayRiemannProof.HeightThirteen
