import Mathlib

/-!
# O operador de empurrão sobre as alturas das lombadas: contagem, álgebra e o limiar da janela

Numa janela com lombadas indexadas por `s : Finset ι`, de alturas `h : ι → ℝ` (as do lado empurrado), o empurrão `ε`
engole cada lombada de altura `< ε` e tira dois zeros da reta (`Forca.lombada_reais_iff`, lombada a lombada). Aqui
fica o operador de contagem e o que se prova sobre ele, sem números:

* `fora s h ε = 2·#{j ∈ s : h j < ε}`: os zeros que o empurrão tira da reta;
* `fora_mono`: empurrão maior, mais zeros fora;
* `fora_eq_zero_iff`, `limiar_da_janela`: nenhum zero sai ⟺ `ε ≤` a lombada mais baixa da janela;
* `fora_total`: acima da lombada mais alta, todos saem;
* `fora_uniao`: janelas disjuntas somam;
* `fora_composta`: dois empurrões seguidos são um só (`ε` e depois `δ` é `ε + δ`): os empurrões formam um semigrupo
  de translações agindo nas alturas;
* `minimo_desce`: a lombada mais baixa só desce quando a janela cresce;
* `empurrao_fixo_acaba_tirando`: se a lombada mais baixa tende a 0 ao longo das janelas (a lei observada:
  1,03·10⁻³ em 41 393 zeros, 5,3·10⁻⁵ em 2 095 776), todo empurrão fixo `ε > 0` acaba tirando zeros da reta.
  A hipótese é a lei dos dados, não um teorema sobre `ζ`.

Nada aqui prova ou refuta RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Empurrao

open Finset Filter Topology

variable {ι : Type*}

/-- **Zeros tirados da reta pelo empurrão `ε`**: dois por lombada de altura `< ε`. -/
noncomputable def fora (s : Finset ι) (h : ι → ℝ) (ε : ℝ) : ℕ := 2 * (s.filter (fun j => h j < ε)).card

/-- Empurrão maior, mais zeros fora. -/
theorem fora_mono (s : Finset ι) (h : ι → ℝ) {ε ε' : ℝ} (hε : ε ≤ ε') : fora s h ε ≤ fora s h ε' := by
  unfold fora
  apply Nat.mul_le_mul_left
  apply Finset.card_le_card
  intro j hj
  rw [Finset.mem_filter] at hj ⊢
  exact ⟨hj.1, lt_of_lt_of_le hj.2 hε⟩

/-- **Nenhum zero sai ⟺ o empurrão não passa de nenhuma lombada.** -/
theorem fora_eq_zero_iff (s : Finset ι) (h : ι → ℝ) (ε : ℝ) : fora s h ε = 0 ↔ ∀ j ∈ s, ε ≤ h j := by
  constructor
  · intro h0 j hj
    by_contra hlt
    push_neg at hlt
    have hmem : j ∈ s.filter (fun j => h j < ε) := Finset.mem_filter.mpr ⟨hj, hlt⟩
    have hpos := Finset.card_pos.mpr ⟨j, hmem⟩
    unfold fora at h0
    omega
  · intro hall
    unfold fora
    have hvazio : s.filter (fun j => h j < ε) = ∅ :=
      Finset.filter_eq_empty_iff.mpr (fun j hj => not_lt.mpr (hall j hj))
    rw [hvazio, Finset.card_empty]

/-- **Limiar da janela**: nenhum zero sai ⟺ `ε` não passa da lombada mais baixa. -/
theorem limiar_da_janela (s : Finset ι) (hne : s.Nonempty) (h : ι → ℝ) (ε : ℝ) :
    fora s h ε = 0 ↔ ε ≤ s.inf' hne h := by
  rw [fora_eq_zero_iff, Finset.le_inf'_iff]

/-- Acima da lombada mais alta, todos os zeros da janela saem. -/
theorem fora_total (s : Finset ι) (h : ι → ℝ) {ε : ℝ} (hall : ∀ j ∈ s, h j < ε) : fora s h ε = 2 * s.card := by
  unfold fora
  rw [Finset.filter_true_of_mem hall]

/-- Janelas disjuntas somam. -/
theorem fora_uniao [DecidableEq ι] {s₁ s₂ : Finset ι} (h : ι → ℝ) (ε : ℝ) (hd : Disjoint s₁ s₂) :
    fora (s₁ ∪ s₂) h ε = fora s₁ h ε + fora s₂ h ε := by
  unfold fora
  rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hd)]
  ring

/-- **Dois empurrões são um só**: empurrar `ε` (as alturas descem `ε`) e depois `δ` é empurrar `ε + δ`. -/
theorem fora_composta (s : Finset ι) (h : ι → ℝ) (ε δ : ℝ) :
    fora s (fun j => h j - ε) δ = fora s h (ε + δ) := by
  unfold fora
  have e : s.filter (fun j => h j - ε < δ) = s.filter (fun j => h j < ε + δ) :=
    Finset.filter_congr (fun j _ => by constructor <;> intro hj <;> linarith)
  rw [e]

/-- **A lombada mais baixa só desce quando a janela cresce.** -/
theorem minimo_desce {s₁ s₂ : Finset ι} (h : ι → ℝ) (hsub : s₁ ⊆ s₂) (hne : s₁.Nonempty) :
    s₂.inf' (hne.mono hsub) h ≤ s₁.inf' hne h := by
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' hne h
  rw [hjeq]
  exact Finset.inf'_le h (hsub hj)

/-- **Todo empurrão fixo acaba tirando zeros da reta** quando a lombada mais baixa das janelas tende a 0. -/
theorem empurrao_fixo_acaba_tirando {s : ℕ → Finset ι} (h : ι → ℝ) (hne : ∀ n, (s n).Nonempty)
    (hlim : Tendsto (fun n => (s n).inf' (hne n) h) atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, 0 < fora (s n) h ε := by
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
  rcases Nat.eq_zero_or_pos (fora (s n) h ε) with h0 | hpos
  · exfalso
    have := (limiar_da_janela (s n) (hne n) h ε).mp h0
    linarith
  · exact hpos

end ClayRiemannProof.Empurrao
