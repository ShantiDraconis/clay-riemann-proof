import ClayRiemannProof.Turing

/-!
# Unicidade por simetria: verificar zeros na reta sem contar zeros

`Turing.lean` prova a lógica clássica: trocas de sinal de `Z` dão zeros na reta, e se a janela tem **no máximo
`k` zeros** (a contagem `N(T₂) − N(T₁)`), os `k` achados esgotam a janela. Essa contagem exige o princípio do
argumento para ζ, que não está na Mathlib. Por isso a janela certificada pela Arb ainda não liga ao kernel.

Este arquivo prova uma segunda rota, **local**, que dispensa a contagem:

* **Unicidade** (`injetiva_de_derivada`): se `‖f′(z) − f′(c)‖ ≤ ε < ‖f′(c)‖` numa bola, `f` é injetiva nela
  (desigualdade do valor médio).
* **Simetria + unicidade ⟹ reta** (`zero_na_bola_simetrica`): numa bola centrada na reta onde ζ é injetiva, todo
  zero está na reta. A torção `s ↦ 1 − s̄` leva a bola nela mesma (`torcao_mem_ball`) e leva zero em zero, e a
  injetividade força o zero a ser fixo. Com uma troca de sinal de `Z` dentro da bola, o zero existe, é único e
  está na reta (`zero_unico_na_bola`).
* **Janelas e mundos sem contagem** (`janelaNaReta_de_bolas`, `rhAteZ_de_bolas`): se todo zero da janela cai numa
  dessas bolas, a janela está na reta. As bolas, a cota da derivada e a cobertura (`|ζ| > 0` fora das bolas) são
  certificados numéricos finitos, do mesmo tipo dos 930 que já fecham a altura 13 no kernel.
* **A junção, lado dos primos** (`logDeriv_completada`): `Λ′/Λ(s) = −Σ Λ(n) n^{−s} − (Γℝ⁻¹)′/Γℝ⁻¹(s)` para
  `Re s > 1`. O lado dos zeros, `Σ_ρ 1/(s − ρ)`, é o produto de Hadamard (`Fronteira/Hadamard.lean`, enunciado).
  É onde as frentes de Li, de de Bruijn–Newman e de Turing se encontram.

Nada aqui prova RH. `OPEN_MATH = true`.
-/
namespace ClayRiemannProof.Verification

open Complex ComplexConjugate Set Metric Filter Topology ClayRiemannProof.Zeta.Symmetry ClayRiemannProof.Turing
open scoped LSeries.notation ArithmeticFunction.vonMangoldt

/-! ## 1. Unicidade -/

/-- **Derivada quase constante ⟹ injetiva**: `‖f′(z) − f′(c)‖ ≤ ε < ‖f′(c)‖` na bola. -/
theorem injetiva_de_derivada {f : ℂ → ℂ} {c : ℂ} {r ε : ℝ}
    (hf : ∀ z ∈ ball c r, DifferentiableAt ℂ f z)
    (hd : ∀ z ∈ ball c r, ‖deriv f z - deriv f c‖ ≤ ε) (hε : ε < ‖deriv f c‖) :
    InjOn f (ball c r) := by
  intro x hx y hy hxy
  by_contra hne
  set g : ℂ → ℂ := fun z => f z - deriv f c * z with hg
  have hgd : ∀ z ∈ ball c r, HasDerivAt g (deriv f z - deriv f c) z := by
    intro z hz
    have h1 := (hf z hz).hasDerivAt.sub ((hasDerivAt_id z).const_mul (deriv f c))
    rw [mul_one] at h1
    exact h1
  have hmv := (convex_ball c r).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hgd z hz).differentiableAt)
    (fun z hz => by rw [(hgd z hz).deriv]; exact hd z hz) hx hy
  have e : g y - g x = -(deriv f c) * (y - x) := by
    simp only [hg]
    rw [hxy]
    ring
  rw [e, norm_mul, norm_neg] at hmv
  have hpos : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
  have := le_of_mul_le_mul_right hmv hpos
  linarith

/-- A torção é uma isometria que fixa todo ponto da reta: `‖torcao z − c‖ = ‖z − c‖` se `Re c = ½`. -/
theorem norm_torcao_sub {c : ℂ} (hc : c.re = 1 / 2) (z : ℂ) : ‖torcao z - c‖ = ‖z - c‖ := by
  have e : torcao z - c = conj (c - z) := by
    apply Complex.ext
    · simp [torcao, hc]; ring
    · simp [torcao]; ring
  rw [e, Complex.norm_conj, norm_sub_rev]

theorem torcao_mem_ball {c : ℂ} (hc : c.re = 1 / 2) {r : ℝ} {z : ℂ} (hz : z ∈ ball c r) :
    torcao z ∈ ball c r := by
  rw [mem_ball, dist_eq_norm] at hz ⊢
  rwa [norm_torcao_sub hc]

/-- **Simetria + unicidade ⟹ reta**: numa bola centrada na reta onde ζ é injetiva, todo zero não trivial está
na reta. -/
theorem zero_na_bola_simetrica {c : ℂ} {r : ℝ} (hc : c.re = 1 / 2)
    (hinj : InjOn riemannZeta (ball c r)) {ρ : ℂ} (hρ : ρ ∈ ball c r) (hz : ρ ∈ Z) : ρ.re = 1 / 2 := by
  have h1 : riemannZeta (torcao ρ) = riemannZeta ρ := by rw [(torcao_mem_Z hz).1, hz.1]
  exact (torcao_fixo_iff ρ).mp (hinj (torcao_mem_ball hc hρ) hρ h1)

/-- **Exatamente um zero na bola, e na reta**: troca de sinal de `Z` em `[a, b]`, segmento dentro da bola, ζ
injetiva na bola. -/
theorem zero_unico_na_bola {c : ℂ} {r a b : ℝ} (hinj : InjOn riemannZeta (ball c r))
    (hab : a ≤ b) (hs : hardyZ a * hardyZ b < 0) (hseg : ∀ t ∈ Icc a b, naReta t ∈ ball c r) :
    ∃ t ∈ Ioo a b, riemannZeta (naReta t) = 0 ∧ ∀ ρ ∈ ball c r, riemannZeta ρ = 0 → ρ = naReta t := by
  obtain ⟨t, ht, h0⟩ := zero_em_aberto hab hs
  have hz : riemannZeta (naReta t) = 0 := (naReta_mem_Z h0).1
  exact ⟨t, ht, hz, fun ρ hρ hρz => hinj hρ (hseg t (Ioo_subset_Icc_self ht)) (by rw [hρz, hz])⟩

/-! ## 2. Janelas e mundos sem contagem -/

/-- **Janela na reta sem contagem**: se todo zero da janela `(T₁, T₂]` está numa das bolas (centradas na reta,
com ζ injetiva), a janela está na reta. Junto com `Turing.rhateZ_estende`, estende os mundos finitos. -/
theorem janelaNaReta_de_bolas {T₁ T₂ : ℝ} (B : List (ℂ × ℝ)) (hc : ∀ p ∈ B, p.1.re = 1 / 2)
    (hinj : ∀ p ∈ B, InjOn riemannZeta (ball p.1 p.2))
    (hcov : ∀ s ∈ Janela T₁ T₂, ∃ p ∈ B, s ∈ ball p.1 p.2) : JanelaNaReta T₁ T₂ := by
  intro s hs
  obtain ⟨p, hp, hsp⟩ := hcov s hs
  exact zero_na_bola_simetrica (hc p hp) (hinj p hp) hsp hs.1

/-- **RH até a altura `T` a partir de certificados locais**: se todo zero não trivial com `|Im s| ≤ T` está numa
das bolas (centradas na reta, com ζ injetiva), então RH vale até `T`. -/
theorem rhAteZ_de_bolas {T : ℕ} (B : List (ℂ × ℝ)) (hc : ∀ p ∈ B, p.1.re = 1 / 2)
    (hinj : ∀ p ∈ B, InjOn riemannZeta (ball p.1 p.2))
    (hcov : ∀ s ∈ Z, |s.im| ≤ T → ∃ p ∈ B, s ∈ ball p.1 p.2) : FiniteWorlds.RHateZ T := by
  intro s hz ht _ him
  have hmem : s ∈ Z := (mem_Z_iff_nao_trivial s).mpr ⟨hz, ht⟩
  obtain ⟨p, hp, hsp⟩ := hcov s hmem him
  exact zero_na_bola_simetrica (hc p hp) (hinj p hp) hsp hmem

/-! ## 3. A junção, lado dos primos -/

/-- **`Λ′/Λ = −Σ Λ(n) n^{−s} − (Γℝ⁻¹)′/Γℝ⁻¹`** para `Re s > 1`: a derivada logarítmica da zeta completada pelo lado
dos primos. -/
theorem logDeriv_completada {s : ℂ} (hs : 1 < s.re) :
    logDeriv completedRiemannZeta s = -L ↗Λ s - logDeriv (fun z => (Gammaℝ z)⁻¹) s := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp at hs
    linarith
  have hs1 : s ≠ 1 := by
    rintro rfl
    simp at hs
  have hev : riemannZeta =ᶠ[𝓝 s] (completedRiemannZeta * fun z => (Gammaℝ z)⁻¹) := by
    filter_upwards [eventually_ne_nhds hs0] with z hz
    rw [riemannZeta_def_of_ne_zero hz, div_eq_mul_inv]
    rfl
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hΛ : completedRiemannZeta s ≠ 0 := by
    intro h
    apply hζ
    rw [riemannZeta_def_of_ne_zero hs0, h, zero_div]
  have hmul := logDeriv_mul (f := completedRiemannZeta) (g := fun z => (Gammaℝ z)⁻¹) s hΛ
    (inv_ne_zero hΓ) (differentiableAt_completedZeta hs0 hs1) (differentiable_Gammaℝ_inv s)
  have hlz : logDeriv riemannZeta s = -L ↗Λ s := by
    rw [logDeriv_apply, ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
    ring
  have heq : logDeriv riemannZeta s =
      logDeriv (completedRiemannZeta * fun z => (Gammaℝ z)⁻¹) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [heq, hmul] at hlz
  linear_combination hlz

end ClayRiemannProof.Verification
