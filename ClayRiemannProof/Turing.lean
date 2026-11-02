import ClayRiemannProof.FiniteWorlds
import Mathlib.NumberTheory.LSeries.HardyZ

/-!
# A lógica do método de Turing: como se verifica RH numa janela de alturas

Toda verificação de RH até uma altura (Turing, Lehmer, Brent, van de Lune, Gourdon, Platt–Trudgian, e a Arb de
FLINT) usa o mesmo argumento, em duas metades:

1. **Detector**: `Z(t) = Λ(½ + it)/|Γ_ℝ(½ + it)|` é real e contínua (`hardyZ` da Mathlib). Uma troca de sinal de `Z`
   entre `a` e `b` dá um zero de `ζ` **na reta** entre `a` e `b` (`zero_em_aberto`). `k` trocas de sinal
   consecutivas dão `k` zeros distintos na reta (`trocas_de_sinal`).
2. **Contagem**: se a janela de alturas `(T₁, T₂]` tem no máximo `k` zeros na faixa, contando todos os `σ`, e o
   detector achou `k` zeros na reta dentro dela, então **todo** zero da janela está na reta, inclusive em `σ = 0,7`,
   `0,283` ou qualquer outro valor (`turing_logica`, `turing_janela`). A cota `k = N(T₂) − N(T₁)` é o que o método de
   Turing certifica.

Este arquivo prova as duas metades e a colagem de janelas no kernel. Também mostra que janelas verificadas
estendem o mundo finito certificado (`rhateZ_estende`). Os números de uma janela concreta (sinais de `Z` e a
contagem) vêm de fora do kernel; ver `computations/zeros/`.

Nada aqui prova RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Turing

open Complex ClayRiemannProof.Zeta.Symmetry ClayRiemannProof.FiniteWorlds

/-! ## 1. O detector -/

/-- O ponto `½ + it` da reta crítica. -/
noncomputable def naReta (t : ℝ) : ℂ := 1 / 2 + t * I

theorem naReta_re (t : ℝ) : (naReta t).re = 1 / 2 := by simp [naReta]

theorem naReta_im (t : ℝ) : (naReta t).im = t := by simp [naReta]

theorem naReta_injective : Function.Injective naReta := fun a b h => by
  simpa [naReta_im] using congrArg Complex.im h

/-- Um zero de `Z` é um zero de `ζ` na faixa, sobre a reta. -/
theorem naReta_mem_Z {t : ℝ} (h : hardyZ t = 0) : naReta t ∈ Z :=
  ⟨(hardyZ_eq_zero_iff t).mp h, by rw [naReta_re]; norm_num, by rw [naReta_re]; norm_num⟩

/-- **Detector**: `Z(a) Z(b) < 0` dá um zero de `ζ` na reta com altura estritamente entre `a` e `b`. -/
theorem zero_em_aberto {a b : ℝ} (hab : a ≤ b) (h : hardyZ a * hardyZ b < 0) :
    ∃ t ∈ Set.Ioo a b, hardyZ t = 0 := by
  have ha : hardyZ a ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact lt_irrefl 0 h
  have hb : hardyZ b ≠ 0 := fun h0 => by rw [h0, mul_zero] at h; exact lt_irrefl 0 h
  obtain ⟨t, ht, hz⟩ : ∃ t ∈ Set.Icc a b, hardyZ t = 0 := by
    rcases mul_neg_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact intermediate_value_Icc' hab continuous_hardyZ.continuousOn ⟨h2.le, h1.le⟩
    · exact intermediate_value_Icc hab continuous_hardyZ.continuousOn ⟨h1.le, h2.le⟩
  refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, hz⟩
  · rintro rfl; exact ha hz
  · rintro rfl; exact hb hz

/-- **`k` trocas de sinal consecutivas dão `k` zeros distintos na reta** entre o primeiro e o último ponto. -/
theorem trocas_de_sinal {k : ℕ} (t : Fin (k + 1) → ℝ) (ht : StrictMono t)
    (hs : ∀ i : Fin k, hardyZ (t i.castSucc) * hardyZ (t i.succ) < 0) :
    ∃ L : Finset ℝ, L.card = k ∧ ∀ x ∈ L, t 0 < x ∧ x < t (Fin.last k) ∧ hardyZ x = 0 := by
  have hex : ∀ i : Fin k, ∃ x ∈ Set.Ioo (t i.castSucc) (t i.succ), hardyZ x = 0 := fun i =>
    zero_em_aberto (ht.monotone (Fin.castSucc_lt_succ (i := i)).le) (hs i)
  choose z hz hz0 using hex
  have hmono : StrictMono z := by
    intro i j hij
    calc z i < t i.succ := (hz i).2
      _ ≤ t j.castSucc := ht.monotone (Fin.succ_le_castSucc_iff.mpr hij)
      _ < z j := (hz j).1
  refine ⟨Finset.univ.image z, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_univ, Fintype.card_fin]
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨lt_of_le_of_lt (ht.monotone (Fin.zero_le _)) (hz i).1,
      lt_of_lt_of_le (hz i).2 (ht.monotone (Fin.le_last _)), hz0 i⟩

/-! ## 2. A contagem -/

/-- Os zeros da faixa com altura na janela `(T₁, T₂]`. -/
def Janela (T₁ T₂ : ℝ) : Set ℂ := {s | s ∈ Z ∧ T₁ < s.im ∧ s.im ≤ T₂}

/-- **RH na janela** `(T₁, T₂]`. -/
def JanelaNaReta (T₁ T₂ : ℝ) : Prop := ∀ s ∈ Janela T₁ T₂, s.re = 1 / 2

/-- **A lógica de Turing**: no máximo `k` zeros na janela, contando todos os `σ`, e `k` zeros distintos achados na
reta dentro dela implicam todos os zeros da janela na reta. -/
theorem turing_logica {T₁ T₂ : ℝ} {k : ℕ} (hN : (Janela T₁ T₂).encard ≤ k) (L : Finset ℝ)
    (hLk : L.card = k) (hL : ∀ x ∈ L, T₁ < x ∧ x ≤ T₂ ∧ hardyZ x = 0) : JanelaNaReta T₁ T₂ := by
  set M : Set ℂ := naReta '' (L : Set ℝ) with hM
  have hMsub : M ⊆ Janela T₁ T₂ := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨h1, h2, h0⟩ := hL x hx
    exact ⟨naReta_mem_Z h0, by rw [naReta_im]; exact h1, by rw [naReta_im]; exact h2⟩
  have hMcard : M.encard = k := by
    rw [hM, naReta_injective.encard_image, Set.encard_coe_eq_coe_finsetCard, hLk]
  have hMfin : M.Finite := (L.finite_toSet).image _
  have hEq : M = Janela T₁ T₂ := hMfin.eq_of_subset_of_encard_le hMsub (by rw [hMcard]; exact hN)
  intro s hs
  rw [← hEq] at hs
  obtain ⟨x, -, rfl⟩ := hs
  exact naReta_re x

/-- **Verificação de uma janela**: pontos `T₁ ≤ t₀ < ⋯ < t_k ≤ T₂` com `k` trocas de sinal de `Z` e a contagem
`#zeros ≤ k` dão RH na janela. -/
theorem turing_janela {T₁ T₂ : ℝ} {k : ℕ} (t : Fin (k + 1) → ℝ) (ht : StrictMono t)
    (hs : ∀ i : Fin k, hardyZ (t i.castSucc) * hardyZ (t i.succ) < 0)
    (h1 : T₁ ≤ t 0) (h2 : t (Fin.last k) ≤ T₂) (hN : (Janela T₁ T₂).encard ≤ k) :
    JanelaNaReta T₁ T₂ := by
  obtain ⟨L, hLk, hL⟩ := trocas_de_sinal t ht hs
  refine turing_logica hN L hLk fun x hx => ?_
  obtain ⟨hx1, hx2, hx0⟩ := hL x hx
  exact ⟨lt_of_le_of_lt h1 hx1, (lt_of_lt_of_le hx2 h2).le, hx0⟩

/-! ## 3. Colagem e extensão do mundo certificado -/

/-- Janelas vizinhas verificadas se colam. -/
theorem janelas_colam {T₁ T₂ T₃ : ℝ} (h12 : JanelaNaReta T₁ T₂) (h23 : JanelaNaReta T₂ T₃) :
    JanelaNaReta T₁ T₃ := by
  rintro s ⟨hs, h1, h3⟩
  rcases le_or_gt s.im T₂ with h | h
  · exact h12 s ⟨hs, h1, h⟩
  · exact h23 s ⟨hs, h, h3⟩

/-- **Extensão do mundo**: RH até `Z₀` mais a janela `(Z₀, Z₁]` dão RH até `Z₁` (as alturas negativas vêm pelo
espelho `s ↦ s̄`). -/
theorem rhateZ_estende {Z₀ Z₁ : ℕ} (h0 : RHateZ Z₀) (hJ : JanelaNaReta Z₀ Z₁) : RHateZ Z₁ := by
  intro s hz ht hs1 him
  have hmem : s ∈ Z := (mem_Z_iff_nao_trivial s).mpr ⟨hz, ht⟩
  rcases le_or_gt |s.im| Z₀ with h | h
  · exact h0 s hz ht hs1 h
  · rcases lt_abs.mp h with hpos | hneg
    · exact hJ s ⟨hmem, hpos, (le_abs_self _).trans him⟩
    · have he := espelho_mem_Z hmem
      have hre := hJ (espelho s) ⟨he, by simp [espelho]; linarith,
        by simp [espelho]; linarith [neg_abs_le s.im, abs_le.mp him]⟩
      simpa [espelho] using hre

/-- No mundo finito: `RHnoMundo Z₀` e a janela `(Z₀, Z₁]` dão `RHnoMundo Z₁`. -/
theorem rhNoMundo_estende {Z₀ Z₁ : ℕ} (h0 : RHnoMundo Z₀) (hJ : JanelaNaReta Z₀ Z₁) : RHnoMundo Z₁ :=
  (rhNoMundo_iff Z₁).mpr (rhateZ_estende ((rhNoMundo_iff Z₀).mp h0) hJ)

end ClayRiemannProof.Turing
