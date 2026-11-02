import ClayRiemannProof.Zeta.Bounds
import ClayRiemannProof.Zeta.Symmetry

/-!
# Uma região sem zeros que alcança o meio: nenhum zero na faixa com `(Im s)² < 3/4`

* `zeta_ne_zero_disco`: **`ζ(s) ≠ 0` sempre que `Re s > 0` e `|s − 1| < 2·Re s`**. Vem de
  `ζ(s) = s/(s−1) − s·H(s)` com `|H(s)| ≤ 1/(2 Re s)` (`ClayRiemannProof.Zeta.Bounds.norm_H_le`, `Hr_le`).
  A região contém o segmento real `(1/3, ∞)` e, na reta crítica, `|Im s| < √3/2`.
* `zeta_ne_zero_baixo` (com a tensão `s ↦ 1 − s`): **nenhum zero na faixa `0 < Re s < 1` com `(Im s)² < 3/4`**.

É a faixa baixa usada por `ClayRiemannProof.HeightThirteen.faixa_sem_zeros`; acima dela, até a altura 13, entram
os certificados de `ClayRiemannProof/CertifiedZeros/`.

Origem: ATK kernel (espelho público, M-Core `390e378`), trecho de `ATK/ZetaRetangulo.lean`
(`zeta_ne_zero_disco`, `zeta_ne_zero_baixo`); portado para Mathlib `8fe7ce4`, nomes `ATK.ZetaRetangulo.*` →
`ClayRiemannProof.LowStrip.Disc.*`, linhas `#print axioms` retiradas (os axiomas estão fixados em
`ClayRiemannProof/AuditThirteen.lean`). `Hr`, `norm_H_le` e `Hr_le` do mesmo arquivo já estavam portados em
`ClayRiemannProof/Zeta/Bounds.lean` e são reusados; `tensao`, `Z`, `tensao_mem_Z` e `re_tensao` vêm de
`ClayRiemannProof/Zeta/Symmetry.lean`. O resto (`RiemannAte`, `riemannAte_raiz`, …) não foi portado.
-/

open Complex Set MeasureTheory Filter Topology

namespace ClayRiemannProof.LowStrip.Disc

open ClayRiemannProof.Zeta.Strip ClayRiemannProof.Zeta.Symmetry ClayRiemannProof.Zeta.Bounds

/-- **Região sem zeros: `ζ(s) ≠ 0` se `Re s > 0` e `|s − 1| < 2·Re s`.** -/
theorem zeta_ne_zero_disco {s : ℂ} (hs : 0 < s.re) (h1 : ‖s - 1‖ < 2 * s.re) :
    riemannZeta s ≠ 0 := by
  intro hz
  rcases le_or_gt 1 s.re with hre | hre
  · exact riemannZeta_ne_zero_of_one_le_re hre hz
  have hs1 : s ≠ 1 := by intro h; rw [h, one_re] at hre; exact lt_irrefl _ hre
  have hH := H_eq_zeta hs hs1
  rw [hz, zero_div, sub_zero] at hH
  have hn : 0 < ‖s - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs1)
  have h2 : ‖H s‖ = 1 / ‖s - 1‖ := by rw [hH, norm_div, norm_one]
  have h3 := (norm_H_le (s := s)).trans (Hr_le hs)
  rw [h2] at h3
  have := (one_div_le_one_div hn (by positivity)).mp h3
  linarith

/-- **Nenhum zero na faixa com `(Im s)² < 3/4`.** -/
theorem zeta_ne_zero_baixo {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (ht : s.im ^ 2 < 3 / 4) :
    riemannZeta s ≠ 0 := by
  have key : ∀ w : ℂ, 1 / 2 ≤ w.re → w.im ^ 2 < 3 / 4 → riemannZeta w ≠ 0 := by
    intro w hw0 hwt
    apply zeta_ne_zero_disco (by linarith)
    have hsq : ‖w - 1‖ ^ 2 = (w.re - 1) ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
    have hlt : ‖w - 1‖ ^ 2 < (2 * w.re) ^ 2 := by
      rw [hsq]
      nlinarith [mul_nonneg (sub_nonneg.mpr hw0) (by linarith : (0 : ℝ) ≤ 3 * w.re + 7 / 2)]
    exact (sq_lt_sq₀ (norm_nonneg _) (by linarith)).mp hlt
  rcases le_or_gt (1 / 2) s.re with h | h
  · exact key s h ht
  · intro hz
    have h2 := tensao_mem_Z (⟨hz, h0, h1⟩ : s ∈ Z)
    have him : (tensao s).im ^ 2 = s.im ^ 2 := by
      unfold tensao; simp only [sub_im, one_im, zero_sub, neg_sq]
    exact key (tensao s) (by rw [re_tensao]; linarith) (by rw [him]; exact ht) h2.1

end ClayRiemannProof.LowStrip.Disc
