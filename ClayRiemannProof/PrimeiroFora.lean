import ClayRiemannProof.HeightThirteen
import ClayRiemannProof.Turing

/-!
# Se existir zero fora da reta, existe um de altura mínima (e ele está acima de toda altura verificada)

O enunciado é **condicional**: nada aqui afirma que exista zero fora da reta. O que se prova é que a pergunta
"onde estaria o primeiro?" faz sentido:

* **Finitude** (`zeros_finitos`): ζ tem só um número finito de zeros em cada retângulo `[0, 1] × [1, T]`. ζ é
  analítica em `ℂ ∖ {1}`, que é conexo, e não é identicamente nula (`ζ(2) ≠ 0`). Pelo princípio da identidade,
  seus zeros são isolados, e um conjunto compacto de pontos isolados é finito.
* **O primeiro** (`primeiro_fora`): se existe um zero não trivial com `Re ρ ≠ ½`, existe um `ρ*` com `Re ρ* ≠ ½`,
  `Im ρ* > 0` e `Im ρ* ≤ |Im σ|` para todo zero `σ` fora da reta. O mínimo existe porque, até a altura de um zero
  fora da reta, os zeros formam um conjunto finito.
* **Acima de toda altura verificada** (`primeiro_fora_acima`): se RH vale até `W`, então `Im ρ* > W`.
  * `W = 13` é teorema (`primeiro_fora_acima_13`).
  * `W = 3 000 175 332 800` é Platt–Trudgian, hipótese nomeada (`PlattTrudgian2021`).
  * `W = 3 000 175 342 471` acrescenta a janela calculada com Arb, outra hipótese nomeada (`JanelaArb2026`;
    ver `computations/zeros/` e a seção 13 do README).

Nada aqui prova RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.PrimeiroFora

open Complex Set Filter Topology ClayRiemannProof.Zeta.Symmetry ClayRiemannProof.FiniteWorlds

/-! ## 1. Zeros isolados e finitude em retângulos -/

/-- `ℂ ∖ {1}` é conexo. -/
theorem preconexo : IsPreconnected ({1}ᶜ : Set ℂ) :=
  (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num) 1).isPreconnected

/-- ζ é analítica em `ℂ ∖ {1}`. -/
theorem analitica : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := fun _ hz =>
  DifferentiableOn.analyticAt (fun _ hw => (differentiableAt_riemannZeta hw).differentiableWithinAt)
    (isOpen_compl_singleton.mem_nhds hz)

/-- **Zeros isolados**: perto de todo `z ≠ 1`, ζ não se anula fora de `z`. -/
theorem zeros_isolados {z : ℂ} (hz : z ≠ 1) : ∀ᶠ w in 𝓝[≠] z, riemannZeta w ≠ 0 := by
  rcases (analitica z hz).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hU := analitica.eqOn_zero_of_preconnected_of_eventuallyEq_zero preconexo hz h
    have h2 : riemannZeta 2 = 0 := hU (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
    exact riemannZeta_ne_zero_of_one_le_re (by norm_num) h2
  · exact h

/-- **Finitude**: ζ tem só um número finito de zeros no retângulo `[0, 1] × [1, T]`. -/
theorem zeros_finitos (T : ℝ) :
    ((Icc (0 : ℝ) 1 ×ℂ Icc 1 T) ∩ riemannZeta ⁻¹' {0}).Finite := by
  set K := Icc (0 : ℝ) 1 ×ℂ Icc 1 T with hK
  have hK1 : ∀ z ∈ K, z ≠ 1 := by
    rintro z ⟨-, him⟩ rfl
    simp at him
    linarith [him.1]
  have hcont : ContinuousOn riemannZeta K := fun z hz =>
    (differentiableAt_riemannZeta (hK1 z hz)).continuousAt.continuousWithinAt
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hclosed : IsClosed (K ∩ riemannZeta ⁻¹' {0}) :=
    hcont.preimage_isClosed_of_isClosed hKc.isClosed isClosed_singleton
  refine (hKc.of_isClosed_subset hclosed inter_subset_left).finite ?_
  rw [isDiscrete_iff_nhdsNE]
  intro x hx
  rw [inf_principal_eq_bot]
  filter_upwards [zeros_isolados (hK1 x hx.1)] with w hw hmem
  exact hw hmem.2

/-! ## 2. O primeiro zero fora da reta -/

/-- Todo zero não trivial tem `|Im| > 13` (`HeightThirteen`). -/
theorem im_gt_13 {s : ℂ} (hs : s ∈ Z) : 13 < |s.im| := by
  by_contra h
  exact ClayRiemannProof.HeightThirteen.faixa_sem_zeros hs.2.1 hs.2.2 (not_lt.mp h) hs.1

/-- O representante de altura positiva: `s` ou `s̄`. -/
theorem representante {s : ℂ} (hs : s ∈ Z) (hre : s.re ≠ 1 / 2) :
    ∃ s' ∈ Z, s'.re ≠ 1 / 2 ∧ s'.im = |s.im| := by
  rcases le_or_gt 0 s.im with h | h
  · exact ⟨s, hs, hre, (abs_of_nonneg h).symm⟩
  · refine ⟨espelho s, espelho_mem_Z hs, by simpa [espelho] using hre, ?_⟩
    simp [espelho, abs_of_neg h]

/-- **Se existe zero fora da reta, existe um de altura mínima.** -/
theorem primeiro_fora (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ 0 < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  obtain ⟨ρ₀, hρ₀, hne₀⟩ := h
  set T := |ρ₀.im| with hT
  set F : Set ℂ := {s | s ∈ Z ∧ s.re ≠ 1 / 2 ∧ 1 ≤ s.im ∧ s.im ≤ T} with hF
  have hsub : F ⊆ (Icc (0 : ℝ) 1 ×ℂ Icc 1 T) ∩ riemannZeta ⁻¹' {0} := by
    rintro s ⟨hs, -, h1, h2⟩
    exact ⟨⟨⟨hs.2.1.le, hs.2.2.le⟩, ⟨h1, h2⟩⟩, hs.1⟩
  have hfin : F.Finite := (zeros_finitos T).subset hsub
  obtain ⟨ρ₁, hρ₁, hne₁, him₁⟩ := representante hρ₀ hne₀
  have h13 := im_gt_13 hρ₀
  have hne : F.Nonempty := ⟨ρ₁, hρ₁, hne₁, by rw [him₁]; linarith, by rw [him₁]⟩
  obtain ⟨ρ, ⟨hρ, hρre, hρ1, hρT⟩, hmin⟩ := exists_min_image F (fun s => s.im) hfin hne
  refine ⟨ρ, hρ, hρre, by linarith, fun σ hσ hσre => ?_⟩
  obtain ⟨σ', hσ', hσ're, hσ'im⟩ := representante hσ hσre
  rcases le_or_gt |σ.im| T with hle | hgt
  · have hσ13 := im_gt_13 hσ
    have := hmin σ' ⟨hσ', hσ're, by rw [hσ'im]; linarith, by rw [hσ'im]; exact hle⟩
    rwa [hσ'im] at this
  · linarith

/-- **O primeiro zero fora da reta está acima de toda altura `W` em que RH foi verificada.** -/
theorem primeiro_fora_acima {W : ℕ} (hW : RHateZ W) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (W : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  obtain ⟨ρ, hρ, hre, hpos, hmin⟩ := primeiro_fora h
  refine ⟨ρ, hρ, hre, ?_, hmin⟩
  by_contra hle
  have hle' : |ρ.im| ≤ (W : ℝ) := by rw [abs_of_pos hpos]; exact not_lt.mp hle
  exact hre (hW ρ hρ.1 ((mem_Z_iff_nao_trivial ρ).mp hρ).2
    (fun h1 => by rw [h1] at hρ; exact absurd hρ.2.2 (by simp)) hle')

/-- `W = 13`, sem hipótese. -/
theorem primeiro_fora_acima_13 (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (13 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima (W := 13)
    ((rhNoMundo_iff 13).mp ClayRiemannProof.HeightThirteen.rhNoMundo_13) h
  simpa using this

/-- **Janela calculada com Arb (fora do kernel)**: todos os zeros com
`3 000 175 332 800 < Im s ≤ 3 000 175 342 471` estão na reta (execução 41546782883; README, seção 13).
Hipótese nomeada; **não** é provada aqui. -/
def JanelaArb2026 : Prop := ClayRiemannProof.Turing.JanelaNaReta 3000175332800 3000175342471

/-- Com Platt–Trudgian e a janela: RH até `3 000 175 342 471`. -/
theorem rhAteZ_janela (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) : RHateZ 3000175342471 :=
  ClayRiemannProof.Turing.rhateZ_estende hPT (by exact_mod_cast hJ)

/-- **O primeiro zero fora da reta, se existir, tem `Im > 3 000 175 342 471`** (condicional às duas
verificações numéricas). -/
theorem primeiro_fora_acima_janela (hPT : PlattTrudgian2021) (hJ : JanelaArb2026)
    (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (3000175342471 : ℝ) < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im| := by
  have := primeiro_fora_acima (rhAteZ_janela hPT hJ) h
  simpa using this

end ClayRiemannProof.PrimeiroFora
