import ClayRiemannProof.WeilRota
import ClayRiemannProof.Xi

/-!
# O limite de (C) é `Ξ`: a rota de Hurwitz sem hipótese sobre o limite (§63)

Na §61, `WeilRota.rota_hurwitz_espectral` pede um limite `g` que zere nas alturas dos zeros de `ζ` sem ser
identicamente nulo perto delas. Aqui o limite é concreto: `Ξ(r) = ξ(½ + ir)`, com a `ξ` inteira de `Xi.lean`
(`xi_eq_zero_iff`: os zeros de `ξ` são exatamente os zeros não triviais de `ζ`).

* `Xi`, `differentiable_Xi`, `Xi_altura`: `Ξ` é inteira e `Ξ(r(ρ)) = ξ(ρ)`.
* `rh_iff_Xi_zeros_reais`: **a RH ⟺ `Ξ` só tem zeros reais.**
* `inteira_nao_some`, `produto_nao_some`: uma função inteira não identicamente nula não é identicamente nula perto de
  ponto nenhum, e o produto de duas também não (princípio da identidade).
* `rota_hurwitz_Xi`: se cada `G n` é inteira com todos os zeros reais (A) e `G n → Ξ·E` localmente uniformemente (C),
  com `E` inteira e não identicamente nula, então a RH vale. Não há hipótese sobre o limite além de `E ≢ 0`.
* `rota_hurwitz_Xi_puro`, `rh_iff_rota_Xi`: com `E = 1`, a rota é justa: a RH ⟺ existem funções inteiras com todos os
  zeros reais que convergem localmente uniformemente para `Ξ`.

As contas da §63 indicam que os estados fundamentais de Weil, normalizados, fazem exatamente isso, com
`ĝ*_L(r) ≈ K_L·Ξ(r)·e^{c(L)r²}` e `c(L) → 0`. Isso é observação numérica, não prova: nem (A) em toda escala nem a
convergência estão provadas. Nada aqui prova RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.WeilXi

open Filter Topology Complex ClayRiemannProof.Zeta.Symmetry ClayRiemannProof.WeilRota ClayRiemannProof.Xi

/-- `Ξ(r) = ξ(½ + ir)`. -/
noncomputable def Xi (r : ℂ) : ℂ := xi (naReta r)

theorem differentiable_naReta : Differentiable ℂ naReta := by
  unfold naReta
  fun_prop

theorem differentiable_Xi : Differentiable ℂ Xi :=
  differentiable_xi.comp differentiable_naReta

/-- `½ + i·r(s) = s`. -/
theorem naReta_altura (s : ℂ) : naReta (altura s) = s := by
  have h : I * (-I * (s - 1 / 2)) = s - 1 / 2 := by
    rw [← mul_assoc, mul_neg, I_mul_I, neg_neg, one_mul]
  unfold naReta altura
  rw [h]
  ring

/-- `r(½ + ir) = r`. -/
theorem altura_naReta (r : ℂ) : altura (naReta r) = r := by
  have h : -I * (I * r) = r := by
    rw [← mul_assoc, neg_mul, I_mul_I, neg_neg, one_mul]
  unfold naReta altura
  rw [add_sub_cancel_left, h]

theorem Xi_altura (s : ℂ) : Xi (altura s) = xi s := by
  rw [Xi, naReta_altura]

/-- **A RH ⟺ `Ξ` só tem zeros reais.** -/
theorem rh_iff_Xi_zeros_reais : RiemannHypothesis ↔ ∀ r : ℂ, Xi r = 0 → r.im = 0 := by
  rw [PorQueMeio.rh_iff_reta]
  constructor
  · intro h r hr
    have := h _ ((xi_eq_zero_iff _).mp hr)
    rw [naReta_re] at this
    linarith
  · intro h ρ hρ
    have h1 := h (altura ρ) (by rw [Xi_altura]; exact (xi_eq_zero_iff ρ).mpr hρ)
    rw [altura_im] at h1
    linarith

/-- **Uma função inteira que não é identicamente nula não é identicamente nula perto de ponto nenhum** (princípio da
identidade em `ℂ`, que é conexo). -/
theorem inteira_nao_some {e : ℂ → ℂ} (he : Differentiable ℂ e) (hne : ∃ z, e z ≠ 0) (z : ℂ) :
    ¬ ∀ᶠ w in 𝓝 z, e w = 0 := by
  intro h
  obtain ⟨z₀, hz₀⟩ := hne
  have hA : AnalyticOnNhd ℂ e Set.univ := fun w _ => he.analyticAt w
  exact hz₀ (hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ z) h
    (Set.mem_univ z₀))

/-- **O produto de duas funções inteiras não identicamente nulas não é identicamente nulo perto de ponto nenhum.** -/
theorem produto_nao_some {f e : ℂ → ℂ} (hf : Differentiable ℂ f) (he : Differentiable ℂ e)
    (hfne : ∃ z, f z ≠ 0) (hene : ∃ z, e z ≠ 0) (z : ℂ) : ¬ ∀ᶠ w in 𝓝 z, f w * e w = 0 := by
  apply inteira_nao_some (hf.mul he) _ z
  obtain ⟨z₀, hz₀⟩ := hfne
  have hev : ∀ᶠ w in 𝓝 z₀, f w ≠ 0 := hf.continuous.continuousAt.eventually_ne hz₀
  have hfreq : ∃ᶠ w in 𝓝 z₀, e w ≠ 0 := by
    intro h
    exact inteira_nao_some he hene z₀ (h.mono fun w hw => not_not.mp hw)
  obtain ⟨w, hw1, hw2⟩ := (hfreq.and_eventually hev).exists
  exact ⟨w, mul_ne_zero hw2 hw1⟩

/-- `ξ(0) = ½ ≠ 0`. -/
theorem xi_algum_ne_zero : ∃ z, xi z ≠ 0 :=
  ⟨0, by rw [xi_zero]; norm_num⟩

/-- **A rota de Hurwitz com limite `Ξ·E`**: (A) cada `G n` é inteira com **todos os zeros reais**; (C) `G n → Ξ·E`
localmente uniformemente, com `E` inteira e não identicamente nula. Então a RH vale. -/
theorem rota_hurwitz_Xi {G : ℕ → ℂ → ℂ} {E : ℂ → ℂ} (hG : ∀ n, Differentiable ℂ (G n))
    (hA : ∀ n r, G n r = 0 → r.im = 0) (hE : Differentiable ℂ E) (hE0 : ∃ r, E r ≠ 0)
    (hconv : TendstoLocallyUniformly G (fun r => Xi r * E r) atTop) : RiemannHypothesis := by
  refine rota_hurwitz_espectral hG hA hconv fun ρ hρ => ⟨?_, ?_⟩
  · show Xi (altura ρ) * E (altura ρ) = 0
    rw [Xi_altura, (xi_eq_zero_iff ρ).mpr hρ, zero_mul]
  · have hE' : ∃ z, (E ∘ altura) z ≠ 0 := by
      obtain ⟨r, hr⟩ := hE0
      exact ⟨naReta r, by rw [Function.comp_apply, altura_naReta]; exact hr⟩
    have hn := produto_nao_some differentiable_xi (hE.comp altura_diff) xi_algum_ne_zero hE' ρ
    intro h
    apply hn
    filter_upwards [h] with z hz
    rw [Function.comp_apply, ← Xi_altura]
    exact hz

/-- **A rota de Hurwitz com limite `Ξ`** (`E = 1`). -/
theorem rota_hurwitz_Xi_puro {G : ℕ → ℂ → ℂ} (hG : ∀ n, Differentiable ℂ (G n))
    (hA : ∀ n r, G n r = 0 → r.im = 0) (hconv : TendstoLocallyUniformly G Xi atTop) : RiemannHypothesis :=
  rota_hurwitz_Xi (E := fun _ => 1) hG hA (differentiable_const 1) ⟨0, one_ne_zero⟩ (by simpa using hconv)

/-- **A rota com limite `Ξ` é justa**: a RH ⟺ existem funções inteiras com todos os zeros reais que convergem para `Ξ`
localmente uniformemente. Com a RH, a sequência constante `Ξ` serve; o conteúdo da rota está em achar a sequência sem
supor a RH (os estados fundamentais de Weil, §63). -/
theorem rh_iff_rota_Xi : RiemannHypothesis ↔ ∃ G : ℕ → ℂ → ℂ, (∀ n, Differentiable ℂ (G n)) ∧
    (∀ n r, G n r = 0 → r.im = 0) ∧ TendstoLocallyUniformly G Xi atTop := by
  constructor
  · intro h
    refine ⟨fun _ => Xi, fun _ => differentiable_Xi, fun _ => rh_iff_Xi_zeros_reais.mp h, ?_⟩
    exact (Metric.tendstoUniformly_iff.mpr fun ε hε =>
      Eventually.of_forall fun _ _ => by simpa using hε).tendstoLocallyUniformly
  · rintro ⟨G, hG, hA, hconv⟩
    exact rota_hurwitz_Xi_puro hG hA hconv

end ClayRiemannProof.WeilXi
