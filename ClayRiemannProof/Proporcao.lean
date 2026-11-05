import ClayRiemannProof.Estrutura
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
# A proporção de zeros na reta: o que é 100% e o que 100% não é

A linha de pesquisa que mais andou em 2026 mede **quantos** zeros estão na reta: `N₀(T)/N(T)`, a fração dos zeros com
altura em `(0, T]` que têm `Re = ½`. Este arquivo põe a medida no kernel e prova as duas coisas exatas que se podem
dizer dela sem a teoria analítica que ainda falta:

* `rh_cem_por_cento`: **a RH dá 100%** para `ζ`: `N₀(T)/N(T) → 1`. Usa a finitude dos zeros num compacto
  (`IsCompact.inter_riemannZetaZeros_finite`, Mathlib) e um zero com `Im > 0`.
* `proporcao_le_um`: a proporção nunca passa de 1.
* `cem_por_cento_nao_basta`: **100% não dá a RH**. O modelo `modeloCem` (a reta `½ + in`, `|n| ≥ 14`, mais o
  quarteto `½ ± 3/10 ± 14i`) tem a estrutura inteira da §54 (faixa, `1 − s`, `s̄`, altura `> 13`), proporção
  tendendo a 1, e um quarteto fora da reta.

As contagens aqui são **sem multiplicidade** (`Set.ncard`). Os resultados da literatura contam com multiplicidade e
medem zeros simples na reta, e eles implicam a versão daqui: `N₀ˢ/N_mult ≤ N₀/N_dist`.

O valor conhecido (2026, ainda fora do kernel): `liminf N₀ˢ(T)/N(T) ≥ 0,6725`, isto é, `ProporcaoNaReta Z 0,6725`
segue dele. Formalizar esse valor exige a contagem de Riemann–von Mangoldt, o princípio do argumento e o teorema de
correlação de pares de Montgomery, que não estão na Mathlib. Nada aqui prova RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Proporcao

open Filter Topology Complex ClayRiemannProof.Zeta.Symmetry ClayRiemannProof.Estrutura

/-! ## 1. As definições -/

/-- Os pontos de `W` com altura em `(0, T]`. -/
def ate (W : Set ℂ) (T : ℝ) : Set ℂ := {ρ | ρ ∈ W ∧ 0 < ρ.im ∧ ρ.im ≤ T}

/-- `N(T)`: quantos pontos de `W` há com altura em `(0, T]` (sem multiplicidade). -/
noncomputable def N (W : Set ℂ) (T : ℝ) : ℕ := (ate W T).ncard

/-- `N₀(T)`: quantos desses estão na reta `Re s = ½`. -/
noncomputable def N0 (W : Set ℂ) (T : ℝ) : ℕ := {ρ | ρ ∈ ate W T ∧ ρ.re = 1 / 2}.ncard

/-- A proporção na reta até a altura `T`. -/
noncomputable def proporcao (W : Set ℂ) (T : ℝ) : ℝ := (N0 W T : ℝ) / N W T

/-- **"Pelo menos a fração `c` dos zeros está na reta"**: `liminf_{T→∞} N₀(T)/N(T) ≥ c`. -/
def ProporcaoNaReta (W : Set ℂ) (c : ℝ) : Prop := ∀ ε > 0, ∀ᶠ T in atTop, c - ε ≤ proporcao W T

theorem ProporcaoNaReta.mono {W : Set ℂ} {c c' : ℝ} (h : ProporcaoNaReta W c) (hc : c' ≤ c) :
    ProporcaoNaReta W c' := fun ε hε => (h ε hε).mono fun _ hT => by linarith

theorem N0_le_N {W : Set ℂ} {T : ℝ} (h : (ate W T).Finite) : N0 W T ≤ N W T :=
  Set.ncard_le_ncard (fun _ hρ => hρ.1) h

/-- **A proporção nunca passa de 1.** -/
theorem proporcao_le_um {W : Set ℂ} {T : ℝ} (h : (ate W T).Finite) : proporcao W T ≤ 1 := by
  unfold proporcao
  rcases Nat.eq_zero_or_pos (N W T) with h0 | hpos
  · rw [h0]
    simp
  · rw [div_le_one (by exact_mod_cast hpos)]
    exact_mod_cast N0_le_N h

theorem proporcao_de_tendsto {W : Set ℂ} (h : Tendsto (proporcao W) atTop (𝓝 1)) : ProporcaoNaReta W 1 := by
  intro ε hε
  filter_upwards [h.eventually (Ioi_mem_nhds (show 1 - ε < 1 by linarith))] with T hT
  exact le_of_lt hT

/-- **Se todo ponto está na reta, a proporção é 1** (quando a contagem não é zero). -/
theorem proporcao_um_de_reta {W : Set ℂ} (hW : ∀ ρ ∈ W, ρ.re = 1 / 2) (hN : ∀ᶠ T in atTop, N W T ≠ 0) :
    Tendsto (proporcao W) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hN] with T hT
  have e : N0 W T = N W T := by
    unfold N0 N
    congr 1
    ext ρ
    exact ⟨fun h => h.1, fun h => ⟨h, hW ρ h.1⟩⟩
  show (1 : ℝ) = proporcao W T
  unfold proporcao
  rw [e, div_self (by exact_mod_cast hT)]

/-! ## 2. Para `ζ`: a contagem é finita e positiva, e a RH dá 100% -/

/-- **Há só finitos zeros não triviais até cada altura** (Mathlib: os zeros de `ζ` num compacto são finitos). -/
theorem ate_Z_finita (T : ℝ) : (ate Z T).Finite := by
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ℂ Set.Icc 0 T) := isCompact_Icc.reProdIm isCompact_Icc
  refine hK.inter_riemannZetaZeros_finite.subset ?_
  rintro ρ ⟨⟨hz, h0, h1⟩, hi0, hiT⟩
  exact ⟨Complex.mem_reProdIm.mpr ⟨⟨h0.le, h1.le⟩, ⟨hi0.le, hiT⟩⟩, hz⟩

/-- **A contagem `N(T)` de `ζ` acaba positiva.** -/
theorem N_Z_pos : ∀ᶠ T in atTop, N Z T ≠ 0 := by
  obtain ⟨ρ, hρ⟩ := ClayRiemannProof.CertifiedZeros.FirstZero.Z_nao_vazio
  have h13 := estrutura_Z.altura ρ hρ
  obtain ⟨σ, hσ, hσ0⟩ : ∃ σ ∈ Z, 0 < σ.im := by
    rcases lt_abs.mp h13 with h | h
    · exact ⟨ρ, hρ, by linarith⟩
    · refine ⟨espelho ρ, espelho_mem_Z hρ, ?_⟩
      simp only [espelho, Complex.conj_im]
      linarith
  filter_upwards [eventually_ge_atTop σ.im] with T hT
  rw [N, ← Nat.pos_iff_ne_zero, Set.ncard_pos (ate_Z_finita T)]
  exact ⟨σ, hσ, hσ0, hT⟩

/-- **A RH dá 100%**: com todo zero não trivial na reta, `N₀(T)/N(T) → 1`. -/
theorem rh_cem_por_cento (h : Target) : Tendsto (proporcao Z) atTop (𝓝 1) :=
  proporcao_um_de_reta ((pontes_da_estrutura.out 1 2).mp h) N_Z_pos

theorem rh_proporcao_um (h : Target) : ProporcaoNaReta Z 1 := proporcao_de_tendsto (rh_cem_por_cento h)

theorem proporcao_Z_le_um (T : ℝ) : proporcao Z T ≤ 1 := proporcao_le_um (ate_Z_finita T)

/-! ## 3. O modelo: 100% e um quarteto fora da reta -/

/-- A reta do modelo: `½ + in`, `n` inteiro, `|n| ≥ 14`. -/
def linhaModelo : Set ℂ := {s | s.re = 1 / 2 ∧ ∃ n : ℤ, 14 ≤ |n| ∧ s.im = n}

/-- O modelo: a reta mais o quarteto `½ ± 3/10 ± 14i`. -/
def modeloCem : Set ℂ := modelo ∪ linhaModelo

theorem estrutura_modeloCem : EstruturaDeRiemann modeloCem where
  faixa := by
    rintro ρ (h | ⟨h, -⟩)
    · exact estrutura_modelo.faixa ρ h
    · rw [h]
      norm_num
  fecha_tensao := by
    rintro ρ (h | ⟨hr, n, hn, hi⟩)
    · exact Or.inl (estrutura_modelo.fecha_tensao ρ h)
    · refine Or.inr ⟨?_, -n, by rwa [abs_neg], ?_⟩
      · rw [tensao, Complex.sub_re, Complex.one_re, hr]
        norm_num
      · rw [tensao, Complex.sub_im, Complex.one_im, hi, Int.cast_neg, zero_sub]
  fecha_espelho := by
    rintro ρ (h | ⟨hr, n, hn, hi⟩)
    · exact Or.inl (estrutura_modelo.fecha_espelho ρ h)
    · refine Or.inr ⟨by simp [espelho, hr], -n, by rwa [abs_neg], by simp [espelho, hi]⟩
  altura := by
    rintro ρ (h | ⟨-, n, hn, hi⟩)
    · exact estrutura_modelo.altura ρ h
    · rw [hi]
      have : (14 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]
        exact_mod_cast hn
      linarith

theorem injetiva_reta : Function.Injective (fun k : ℕ => (⟨1 / 2, k⟩ : ℂ)) := fun a b h => by
  simpa using congrArg Complex.im h

/-- Os pontos do modelo na reta até a altura `T` são `½ + ik`, `14 ≤ k ≤ ⌊T⌋`. -/
theorem reta_modeloCem {T : ℝ} (hT : 0 ≤ T) :
    {ρ | ρ ∈ ate modeloCem T ∧ ρ.re = 1 / 2} =
      (fun k : ℕ => (⟨1 / 2, k⟩ : ℂ)) '' (Finset.Icc 14 ⌊T⌋₊ : Set ℕ) := by
  ext ρ
  constructor
  · rintro ⟨⟨hW, hi0, hiT⟩, hr⟩
    rcases hW with hm | ⟨-, n, hn, hi⟩
    · exfalso
      rcases hm.1 with h | h <;> rw [h] at hr <;> norm_num at hr
    · have hn0 : 0 < n := by
        have : (0 : ℝ) < n := by
          rw [← hi]
          exact hi0
        exact_mod_cast this
      have hn14 : 14 ≤ n := by rwa [abs_of_pos hn0] at hn
      have hc : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast Int.toNat_of_nonneg hn0.le
      refine ⟨n.toNat, ?_, ?_⟩
      · simp only [Finset.coe_Icc, Set.mem_Icc]
        constructor
        · omega
        · apply Nat.le_floor
          rw [hc, ← hi]
          exact hiT
      · apply Complex.ext
        · show (1 : ℝ) / 2 = ρ.re
          rw [hr]
        · show ((n.toNat : ℕ) : ℝ) = ρ.im
          rw [hc, hi]
  · rintro ⟨k, hk, rfl⟩
    simp only [Finset.coe_Icc, Set.mem_Icc] at hk
    refine ⟨⟨Or.inr ⟨rfl, k, ?_, by simp⟩, ?_, ?_⟩, rfl⟩
    · rw [abs_of_nonneg (by positivity)]
      exact_mod_cast hk.1
    · show (0 : ℝ) < k
      exact_mod_cast (show 0 < k by omega)
    · show (k : ℝ) ≤ T
      exact (Nat.cast_le.mpr hk.2).trans (Nat.floor_le hT)

theorem ate_modeloCem_sub {T : ℝ} :
    ate modeloCem T ⊆ {ρ | ρ ∈ ate modeloCem T ∧ ρ.re = 1 / 2} ∪ {⟨4 / 5, 14⟩, ⟨1 / 5, 14⟩} := by
  intro ρ hρ
  by_cases hr : ρ.re = 1 / 2
  · exact Or.inl ⟨hρ, hr⟩
  · right
    obtain ⟨hW, hi0, -⟩ := hρ
    rcases hW with ⟨hre, him⟩ | ⟨h, -⟩
    · have him' : ρ.im = 14 := by
        rcases him with h | h
        · exact h
        · rw [h] at hi0
          norm_num at hi0
      rcases hre with h | h
      · exact Or.inl (Complex.ext (by rw [h]; norm_num) him')
      · exact Or.inr (Complex.ext (by rw [h]; norm_num) him')
    · exact absurd h hr

theorem par_distinto : (⟨4 / 5, 14⟩ : ℂ) ≠ ⟨1 / 5, 14⟩ := fun h => by
  have := congrArg Complex.re h
  norm_num at this

/-- As contagens do modelo a partir da altura 14: `N₀ + 13 = ⌊T⌋`, `N₀ ≤ N ≤ N₀ + 2`. -/
theorem contagens_modeloCem {T : ℝ} (hT : 14 ≤ T) :
    N0 modeloCem T + 13 = ⌊T⌋₊ ∧ N0 modeloCem T ≤ N modeloCem T ∧ N modeloCem T ≤ N0 modeloCem T + 2 := by
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hA := reta_modeloCem hT0
  have h14 : 14 ≤ ⌊T⌋₊ := Nat.le_floor (by exact_mod_cast hT)
  have hN0 : N0 modeloCem T = ⌊T⌋₊ + 1 - 14 := by
    rw [N0, hA, Set.ncard_image_of_injective _ injetiva_reta, Set.ncard_coe_finset, Nat.card_Icc]
  have hfinA : {ρ | ρ ∈ ate modeloCem T ∧ ρ.re = 1 / 2}.Finite := by
    rw [hA]
    exact (Finset.finite_toSet _).image _
  have hfinU := hfinA.union (Set.toFinite ({⟨4 / 5, 14⟩, ⟨1 / 5, 14⟩} : Set ℂ))
  have hfin : (ate modeloCem T).Finite := hfinU.subset ate_modeloCem_sub
  refine ⟨by omega, N0_le_N hfin, ?_⟩
  calc N modeloCem T
      ≤ ({ρ | ρ ∈ ate modeloCem T ∧ ρ.re = 1 / 2} ∪ {⟨4 / 5, 14⟩, ⟨1 / 5, 14⟩} : Set ℂ).ncard :=
        Set.ncard_le_ncard ate_modeloCem_sub hfinU
    _ ≤ N0 modeloCem T + ({⟨4 / 5, 14⟩, ⟨1 / 5, 14⟩} : Set ℂ).ncard := Set.ncard_union_le _ _
    _ = N0 modeloCem T + 2 := by rw [Set.ncard_pair par_distinto]

/-- **O modelo tem 100%**: `N₀(T)/N(T) → 1`. -/
theorem cem_por_cento_modelo : Tendsto (proporcao modeloCem) atTop (𝓝 1) := by
  have key : ∀ T : ℝ, 14 ≤ T → (N0 modeloCem T : ℝ) / (N0 modeloCem T + 2) ≤ proporcao modeloCem T ∧
      proporcao modeloCem T ≤ 1 ∧ T - 14 ≤ (N0 modeloCem T : ℝ) := by
    intro T hT
    obtain ⟨h13, hle, hge⟩ := contagens_modeloCem hT
    have hfl := Nat.sub_one_lt_floor T
    have h13r : (N0 modeloCem T : ℝ) + 13 = ⌊T⌋₊ := by exact_mod_cast h13
    have h14 : 14 ≤ ⌊T⌋₊ := Nat.le_floor (by exact_mod_cast hT)
    have hpos0 : 1 ≤ N0 modeloCem T := by omega
    have hposN : (0 : ℝ) < N modeloCem T := by exact_mod_cast (show 0 < N modeloCem T by omega)
    have hger : (N modeloCem T : ℝ) ≤ N0 modeloCem T + 2 := by exact_mod_cast hge
    have hler : (N0 modeloCem T : ℝ) ≤ N modeloCem T := by exact_mod_cast hle
    refine ⟨div_le_div_of_nonneg_left (by positivity) hposN hger, ?_, by linarith⟩
    unfold proporcao
    rw [div_le_one hposN]
    exact hler
  have hx : Tendsto (fun T => (N0 modeloCem T : ℝ)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨max 14 (b + 14), fun T hT => ?_⟩
    have h1 := (key T (le_trans (le_max_left _ _) hT)).2.2
    have h2 := le_trans (le_max_right _ _) hT
    linarith
  have h1 : Tendsto (fun x : ℝ => x / (x + 2)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := (2 : ℝ))).div_atTop (tendsto_atTop_add_const_right atTop 2 tendsto_id))
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have hx2 : x + 2 ≠ 0 := by linarith
    simp only [id_eq]
    field_simp
    ring
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (h1.comp hx) tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 14] with T hT
    exact (key T hT).1
  · filter_upwards [eventually_ge_atTop 14] with T hT
    exact (key T hT).2.1

/-- **100% não dá a RH**: existe um conjunto com a estrutura inteira (faixa, `1 − s`, `s̄`, altura `> 13`), com
proporção na reta tendendo a 1, e um quarteto fora da reta. -/
theorem cem_por_cento_nao_basta : ∃ W : Set ℂ, EstruturaDeRiemann W ∧ Tendsto (proporcao W) atTop (𝓝 1) ∧
    ∃ ρ ∈ W, ρ.re ≠ 1 / 2 :=
  ⟨modeloCem, estrutura_modeloCem, cem_por_cento_modelo, ⟨4 / 5, 14⟩,
    Or.inl ⟨Or.inl (by norm_num), Or.inl rfl⟩, by norm_num⟩

/-- **O resumo**: a RH dá 100% para `ζ`; 100%, mesmo com toda a estrutura, não dá a reta. -/
theorem cem_por_cento : (Target → Tendsto (proporcao Z) atTop (𝓝 1)) ∧
    ¬ ∀ W : Set ℂ, EstruturaDeRiemann W → Tendsto (proporcao W) atTop (𝓝 1) → ∀ ρ ∈ W, ρ.re = 1 / 2 := by
  refine ⟨rh_cem_por_cento, fun h => ?_⟩
  obtain ⟨W, hW, ht, ρ, hρ, hr⟩ := cem_por_cento_nao_basta
  exact hr (h W hW ht ρ hρ)

/-! ## 4. 100% exato até cada altura verificada -/

/-- **Até a altura verificada, a proporção é exatamente 1**: se todo zero não trivial com `|Im| ≤ X` está na reta
(`RHateZ X`), então `N₀(T)/N(T) = 1` para todo `T ≤ X` com `N(T) ≠ 0`. Com a continuação do repositório
(`Continuacao.rhAteZ_continuacao…`, sob as hipóteses nomeadas dos dados da Arb), vale até `≈ 3·10¹²`. -/
theorem proporcao_um_ate {X : ℕ} (h : FiniteWorlds.RHateZ X) {T : ℝ} (hT : T ≤ X) (hN : N Z T ≠ 0) :
    proporcao Z T = 1 := by
  have e : N0 Z T = N Z T := by
    unfold N0 N
    congr 1
    ext ρ
    refine ⟨fun h' => h'.1, fun h' => ⟨h', ?_⟩⟩
    obtain ⟨⟨hz, h0, h1⟩, hi0, hiT⟩ := h'
    refine h ρ hz (not_trivial_of_re_pos h0) (fun e => ?_) ?_
    · rw [e, Complex.one_re] at h1
      exact lt_irrefl _ h1
    · rw [abs_of_pos hi0]
      linarith
  unfold proporcao
  rw [e, div_self (by exact_mod_cast hN)]

/-! ## 5. O esqueleto do método de 2026 -/

/-- **O esqueleto do método**: se `a(T) ≥ 2b(T) − S(T)` (a desigualdade de Bessel de Lamzouri, com `a = N₀ˢ`,
`b = N` e `S = Σ K(γ − γ')²`) e, para todo `ε > 0`, `S(T) ≤ (C + ε)·b(T)` no limite (a correlação de pares, que dá a
constante `C`), então `a/b ≥ 2 − C − ε` no limite. Com o alcance conhecido hoje (`|α| ≤ 1`) o melhor `C` é
`C_MT = ½ + (1/√2)·cot(1/√2) ≈ 1,3275`, e sai `0,6725`; com a correlação de pares até o alcance `A`, `C(A)` cai e a
fração sobe (`computations/proporcao/curva.py`). As duas hipóteses são as camadas que faltam no kernel. -/
theorem esqueleto {a b S : ℝ → ℝ} {C : ℝ} (hab : ∀ᶠ T in atTop, 2 * b T - S T ≤ a T)
    (hS : ∀ ε > 0, ∀ᶠ T in atTop, S T ≤ (C + ε) * b T) (hb : ∀ᶠ T in atTop, 0 < b T) :
    ∀ ε > 0, ∀ᶠ T in atTop, 2 - C - ε ≤ a T / b T := by
  intro ε hε
  filter_upwards [hab, hS ε hε, hb] with T h1 h2 h3
  rw [le_div_iff₀ h3]
  nlinarith

end ClayRiemannProof.Proporcao
