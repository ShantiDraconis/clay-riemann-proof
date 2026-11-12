import ClayRiemannProof.EixoRiemann.Algebra
import ClayRiemannProof.Zeta.Symmetry
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Eixo Riemann em uso: quartetos, `Idem`, `ℂ⁴` e as três conjecturas propostas

O eixo adotado é `Idem` (`e² = e`, 4 componentes reais: `a + b·i + c·e + d·i·e`). Este arquivo confere, no
kernel, o que foi proposto sobre ele.

## Quartetos (geometria pura, incondicional)

* `orbita s = {s, s̄, 1 − s, 1 − s̄}` (grupo de Klein gerado por espelho e tensão).
* `orbita_eq_of_mem`, `orbitas_iguais_ou_disjuntas`: dois quartetos que têm **um** ponto em comum são o mesmo
  quarteto. Não existem quartetos "conectados": a conta `4n − 2k` com `k > 0` nunca acontece.
* `orbita_card`: fora da reta e fora do eixo real, o quarteto tem exatamente 4 pontos.
* `orbita_metade_de_cima`: exatamente 2 deles têm `Im > 0`. Um quarteto soma **2** em `N(T)`, não 4.
* `quartetos_geral`, `zeros_fora_em_quartetos`: todo conjunto finito simétrico de zeros fora da reta tem
  `4k` pontos, `2k` deles na metade de cima. Um zero fora nunca "carrega" 6, 8, 10 ou 12: carrega o seu
  quarteto, e só.

## `Idem`: zero no eixo com `δ ≠ 0` existe

* `Idem.trivial_carrega_trivial` (incondicional): `ζ(−2 + (−2)·e) = (ζ(−2), ζ(−4)) = (0, 0)`, com `δ = −2`.
* `rhIdemProposta_implica_sem_zeros`: a "RH-Idem" proposta (`zero em Idem com 0 < σ < 1, t ≠ 0 ⟹ δ = 0`)
  implica que ζ **não tem nenhum** zero não trivial: o ponto `ρ + (1 − 2ρ)·e` carrega `ρ` e `1 − ρ`. Como ζ
  tem zeros na reta (Hardy, 1914; o primeiro em `t ≈ 14,1347`), a proposta é falsa.
* `rhIdem_iff`: a versão corrigida (`Re z = 1/2` e `Re δ = 0`) é equivalente a RH. É reformulação.
* `Idem.eixo_puro_nunca_zero`, `Idem.eixo_puro_dois`: no eixo puro `0 + w·e` o primeiro componente é
  `ζ(0) = −1/2`, e o coeficiente de `e` é `ζ(w) + 1/2` exato; em `w = 2` ele vale `π²/6 + 1/2 > 0`.

## `ℂ⁴` e `Dual`

* `Q_eq_zero_iff`, `rhQuarteto_iff`: na faixa, `Q(s) = 0 ⟺ ζ(s) = 0`; a "RH-Quarteto" é RH, reescrita.
* `rhDual_iff_zerosSimples`: a "RH-Dual" é a conjectura dos zeros simples, que não é RH.

Nada aqui prova ou refuta RH.
-/

open ClayRiemannProof.Zeta.Symmetry

namespace EixoRiemann

/-! ## 0. Partes real e imaginária das três reflexões -/

theorem re_esp (s : ℂ) : (espelho s).re = s.re := by unfold espelho; simp
theorem im_esp (s : ℂ) : (espelho s).im = -s.im := by unfold espelho; simp
theorem im_ten (s : ℂ) : (tensao s).im = -s.im := by unfold tensao; simp
theorem im_tor (s : ℂ) : (torcao s).im = s.im := by unfold torcao; simp

theorem ten_esp (s : ℂ) : tensao (espelho s) = torcao s := (torcao_eq s).1.symm
theorem esp_ten (s : ℂ) : espelho (tensao s) = torcao s := (torcao_eq s).2.symm
theorem tor_esp (s : ℂ) : torcao (espelho s) = tensao s := by
  rw [(torcao_eq (espelho s)).1, espelho_espelho]
theorem esp_tor (s : ℂ) : espelho (torcao s) = tensao s := by
  rw [(torcao_eq s).2, espelho_espelho]
theorem ten_tor (s : ℂ) : tensao (torcao s) = espelho s := by
  rw [(torcao_eq s).1, tensao_tensao]
theorem tor_ten (s : ℂ) : torcao (tensao s) = espelho s := by
  rw [(torcao_eq (tensao s)).2, tensao_tensao]

/-! ## 1. Quartetos -/

section Quartetos

open scoped Classical

/-- O quarteto de `s`: `{s, s̄, 1 − s, 1 − s̄}`. -/
noncomputable def orbita (s : ℂ) : Finset ℂ := {s, espelho s, tensao s, torcao s}

theorem mem_orbita_self (s : ℂ) : s ∈ orbita s := by simp [orbita]

theorem orbita_espelho (s : ℂ) : orbita (espelho s) = orbita s := by
  ext x
  simp only [orbita, Finset.mem_insert, Finset.mem_singleton, espelho_espelho, ten_esp, tor_esp]
  tauto

theorem orbita_tensao (s : ℂ) : orbita (tensao s) = orbita s := by
  ext x
  simp only [orbita, Finset.mem_insert, Finset.mem_singleton, tensao_tensao, esp_ten, tor_ten]
  tauto

theorem orbita_torcao (s : ℂ) : orbita (torcao s) = orbita s := by
  ext x
  simp only [orbita, Finset.mem_insert, Finset.mem_singleton, torcao_torcao, esp_tor, ten_tor]
  tauto

/-- Cada ponto do quarteto gera o mesmo quarteto. -/
theorem orbita_eq_of_mem {s t : ℂ} (h : t ∈ orbita s) : orbita t = orbita s := by
  simp only [orbita, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl
  · rfl
  · exact orbita_espelho s
  · exact orbita_tensao s
  · exact orbita_torcao s

/-- **Não existem quartetos conectados**: dois quartetos são iguais ou disjuntos. -/
theorem orbitas_iguais_ou_disjuntas (s t : ℂ) :
    orbita s = orbita t ∨ Disjoint (orbita s) (orbita t) := by
  by_cases h : ∃ x, x ∈ orbita s ∧ x ∈ orbita t
  · obtain ⟨x, hs, ht⟩ := h
    left
    rw [← orbita_eq_of_mem hs, ← orbita_eq_of_mem ht]
  · right
    rw [Finset.disjoint_left]
    intro x hs ht
    exact h ⟨x, hs, ht⟩

theorem orbita_im {s x : ℂ} (h : x ∈ orbita s) : x.im = s.im ∨ x.im = -s.im := by
  simp only [orbita, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (im_esp s)
  · exact Or.inr (im_ten s)
  · exact Or.inl (im_tor s)

theorem orbita_re {s x : ℂ} (h : x ∈ orbita s) : x.re = s.re ∨ x.re = 1 - s.re := by
  simp only [orbita, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl (re_esp s)
  · exact Or.inr (re_tensao s)
  · exact Or.inr (re_torcao s)

/-- Fora da reta e fora do eixo real, o quarteto tem 4 pontos distintos. -/
theorem orbita_card {s : ℂ} (hre : s.re ≠ 1 / 2) (him : s.im ≠ 0) : (orbita s).card = 4 := by
  have a : s ≠ espelho s := fun h => him (by
    have := congrArg Complex.im h; rw [im_esp] at this; linarith)
  have b : s ≠ tensao s := fun h => hre (by
    have := congrArg Complex.re h; rw [re_tensao] at this; linarith)
  have c : s ≠ torcao s := fun h => hre (by
    have := congrArg Complex.re h; rw [re_torcao] at this; linarith)
  have d : espelho s ≠ tensao s := fun h => hre (by
    have := congrArg Complex.re h; rw [re_esp, re_tensao] at this; linarith)
  have e : espelho s ≠ torcao s := fun h => him (by
    have := congrArg Complex.im h; rw [im_esp, im_tor] at this; linarith)
  have f : tensao s ≠ torcao s := fun h => him (by
    have := congrArg Complex.im h; rw [im_ten, im_tor] at this; linarith)
  have hA : tensao s ∉ ({torcao s} : Finset ℂ) := by
    rw [Finset.mem_singleton]; exact f
  have hB : espelho s ∉ ({tensao s, torcao s} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨d, e⟩
  have hC : s ∉ ({espelho s, tensao s, torcao s} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨a, b, c⟩
  show ({s, espelho s, tensao s, torcao s} : Finset ℂ).card = 4
  rw [Finset.card_insert_of_notMem hC, Finset.card_insert_of_notMem hB,
    Finset.card_insert_of_notMem hA, Finset.card_singleton]

/-- Uma involução de `S` que troca `p` por `¬p` divide `S` ao meio. -/
theorem card_dobra (S : Finset ℂ) (f : ℂ → ℂ) (hf : ∀ x, f (f x) = x) (hS : ∀ x ∈ S, f x ∈ S)
    (p : ℂ → Prop) [DecidablePred p] (hp : ∀ x ∈ S, (p x ↔ ¬ p (f x))) :
    S.card = 2 * (S.filter p).card := by
  have himg : S.filter (fun x => ¬ p x) = (S.filter p).image f := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hx, hnx⟩
      refine ⟨f x, ⟨hS x hx, ?_⟩, hf x⟩
      by_contra h
      exact hnx ((hp x hx).mpr h)
    · rintro ⟨a, ⟨ha, hpa⟩, rfl⟩
      exact ⟨hS a ha, (hp a ha).mp hpa⟩
  have hinj : Function.Injective f := fun a b h => by rw [← hf a, h, hf b]
  have hc := Finset.card_filter_add_card_filter_not (s := S) p
  rw [himg, Finset.card_image_of_injective _ hinj] at hc
  omega

/-- **Contagem em quartetos** (geometria pura): conjunto finito fechado por espelho e torção, sem pontos na
reta nem no eixo real, tem `4k` pontos, `2k` deles com `Im > 0`. -/
theorem quartetos_geral (S : Finset ℂ) (hesp : ∀ x ∈ S, espelho x ∈ S)
    (htor : ∀ x ∈ S, torcao x ∈ S) (him : ∀ x ∈ S, x.im ≠ 0) (hre : ∀ x ∈ S, x.re ≠ 1 / 2) :
    S.card = 4 * (S.filter (fun x => 0 < x.im ∧ 1 / 2 < x.re)).card ∧
      (S.filter (fun x => 0 < x.im)).card =
        2 * (S.filter (fun x => 0 < x.im ∧ 1 / 2 < x.re)).card := by
  have h1 : S.card = 2 * (S.filter (fun x => 0 < x.im)).card := by
    refine card_dobra S espelho espelho_espelho hesp _ ?_
    intro x hx
    rw [im_esp]
    have := him x hx
    constructor
    · intro h h'
      linarith
    · intro h
      push_neg at h
      exact lt_of_le_of_ne (by linarith) (Ne.symm this)
  have hU : ∀ x ∈ S.filter (fun x => 0 < x.im), torcao x ∈ S.filter (fun x => 0 < x.im) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨htor x hx.1, by rw [im_tor]; exact hx.2⟩
  have h2 : (S.filter (fun x => 0 < x.im)).card =
      2 * ((S.filter (fun x => 0 < x.im)).filter (fun x => 1 / 2 < x.re)).card := by
    refine card_dobra _ torcao torcao_torcao hU _ ?_
    intro x hx
    rw [re_torcao]
    have := hre x (Finset.mem_filter.mp hx).1
    constructor
    · intro h h'
      linarith
    · intro h
      push_neg at h
      exact lt_of_le_of_ne (by linarith) (fun e => this e.symm)
  rw [Finset.filter_filter] at h2
  refine ⟨?_, h2⟩
  rw [h1, h2]
  ring

/-- Um quarteto fora da reta soma exatamente 2 em `N(T)` (os pontos com `Im > 0`). -/
theorem orbita_metade_de_cima {s : ℂ} (hre : s.re ≠ 1 / 2) (him : s.im ≠ 0) :
    ((orbita s).filter (fun x => 0 < x.im)).card = 2 := by
  have hesp : ∀ x ∈ orbita s, espelho x ∈ orbita s := fun x hx => by
    rw [← orbita_eq_of_mem hx]; simp [orbita]
  have htor : ∀ x ∈ orbita s, torcao x ∈ orbita s := fun x hx => by
    rw [← orbita_eq_of_mem hx]; simp [orbita]
  have him' : ∀ x ∈ orbita s, x.im ≠ 0 := fun x hx => by
    rcases orbita_im hx with e | e <;> rw [e] <;> simpa using him
  have hre' : ∀ x ∈ orbita s, x.re ≠ 1 / 2 := fun x hx h' => by
    rcases orbita_re hx with e | e <;> rw [e] at h' <;> apply hre <;> linarith
  obtain ⟨h1, h2⟩ := quartetos_geral (orbita s) hesp htor him' hre'
  rw [orbita_card hre him] at h1
  omega

end Quartetos

/-- **Zeros fora da reta vêm em múltiplos de 4.** Para qualquer `T`, se `S` é (como `Finset`) o conjunto dos
zeros não triviais fora da reta com `|Im| < T`, então `#S = 4k` e `2k` deles têm `Im > 0`. -/
theorem zeros_fora_em_quartetos (T : ℝ) (S : Finset ℂ)
    (hS : ∀ x, x ∈ S ↔ x ∈ Z ∧ x.re ≠ 1 / 2 ∧ |x.im| < T) :
    S.card = 4 * (S.filter (fun x => 0 < x.im ∧ 1 / 2 < x.re)).card ∧
      (S.filter (fun x => 0 < x.im)).card =
        2 * (S.filter (fun x => 0 < x.im ∧ 1 / 2 < x.re)).card := by
  refine quartetos_geral S ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hZ, hre, hT⟩ := (hS x).mp hx
    refine (hS _).mpr ⟨espelho_mem_Z hZ, ?_, ?_⟩
    · rwa [re_esp]
    · rwa [im_esp, abs_neg]
  · intro x hx
    obtain ⟨hZ, hre, hT⟩ := (hS x).mp hx
    refine (hS _).mpr ⟨torcao_mem_Z hZ, ?_, ?_⟩
    · rw [re_torcao]
      intro h
      apply hre
      linarith
    · rwa [im_tor]
  · exact fun x hx => im_ne_zero_of_mem_Z ((hS x).mp hx).1
  · exact fun x hx => ((hS x).mp hx).2.1

/-! ## 2. `Idem`: o eixo adotado -/

/-- **`−2` carrega `−4`** (incondicional): `ζ(−2 + (−2)·e) = (0, 0)` com `δ = −2 ≠ 0`. -/
theorem Idem.trivial_carrega_trivial : Idem.aplica riemannZeta ⟨-2, -2⟩ = ⟨0, 0⟩ := by
  rw [Idem.aplica_eq_zero]
  constructor
  · show riemannZeta (-2) = 0
    simpa using riemannZeta_neg_two_mul_nat_add_one 0
  · show riemannZeta (-2 + -2) = 0
    have h := riemannZeta_neg_two_mul_nat_add_one 1
    norm_num at h ⊢
    exact h

/-- A "RH-Idem" proposta: zero em `Idem` com `0 < σ < 1` e `t ≠ 0` obriga `δ = 0` e `σ = 1/2`. -/
def RHIdemProposta : Prop :=
  ∀ x : Idem, 0 < x.z.re → x.z.re < 1 → x.z.im ≠ 0 →
    Idem.aplica riemannZeta x = ⟨0, 0⟩ → x.w = 0 ∧ x.z.re = 1 / 2

/-- **A RH-Idem proposta apaga todos os zeros**: para `ρ ∈ Z`, o ponto `ρ + (1 − 2ρ)·e` vale `(ζ ρ, ζ(1 − ρ)) =
(0, 0)` com `δ = 1 − 2ρ ≠ 0`. Logo a proposta implica `Z = ∅`, o que é falso (Hardy). -/
theorem rhIdemProposta_implica_sem_zeros : RHIdemProposta → Z = ∅ := by
  intro h
  ext ρ
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hρ
  have him := im_ne_zero_of_mem_Z hρ
  obtain ⟨hz1, -, -⟩ := tensao_mem_Z hρ
  obtain ⟨hz, h0, h1⟩ := hρ
  have hx : Idem.aplica riemannZeta ⟨ρ, 1 - 2 * ρ⟩ = ⟨0, 0⟩ := by
    rw [Idem.aplica_eq_zero]
    refine ⟨hz, ?_⟩
    show riemannZeta (ρ + (1 - 2 * ρ)) = 0
    rw [show ρ + (1 - 2 * ρ) = tensao ρ by unfold tensao; ring]
    exact hz1
  have hw := (h ⟨ρ, 1 - 2 * ρ⟩ h0 h1 him hx).1
  apply him
  have := congrArg Complex.im hw
  simp at this
  linarith

/-- RH na faixa: todo zero com `0 < Re < 1` está na reta. -/
def RHFaixa : Prop := ∀ s ∈ Z, s.re = 1 / 2

/-- A RH-Idem corrigida: zero em `Idem` com os dois pontos na faixa ⟹ `Re z = 1/2` e `Re δ = 0`. -/
def RHIdem : Prop :=
  ∀ x : Idem, Idem.aplica riemannZeta x = ⟨0, 0⟩ → 0 < x.z.re → x.z.re < 1 →
    0 < (x.z + x.w).re → (x.z + x.w).re < 1 → x.z.re = 1 / 2 ∧ x.w.re = 0

/-- **A RH-Idem corrigida é RH**, nem mais nem menos. -/
theorem rhIdem_iff : RHIdem ↔ RHFaixa := by
  constructor
  · intro h s hs
    obtain ⟨hz, h0, h1⟩ := hs
    have hx : Idem.aplica riemannZeta ⟨s, 0⟩ = ⟨0, 0⟩ := by
      rw [Idem.aplica_eq_zero]
      exact ⟨hz, by simpa using hz⟩
    exact (h ⟨s, 0⟩ hx h0 h1 (by simpa using h0) (by simpa using h1)).1
  · intro h x hx h0 h1 h0' h1'
    rw [Idem.aplica_eq_zero] at hx
    have a := h x.z ⟨hx.1, h0, h1⟩
    have b := h (x.z + x.w) ⟨hx.2, h0', h1'⟩
    refine ⟨a, ?_⟩
    rw [Complex.add_re] at b
    linarith

/-- No eixo puro `0 + w·e`, o primeiro componente é sempre `ζ(0) = −1/2`: nunca é zero. -/
theorem Idem.eixo_puro_nunca_zero (w : ℂ) : Idem.aplica riemannZeta ⟨0, w⟩ ≠ ⟨0, 0⟩ := by
  rw [Ne, Idem.aplica_eq_zero]
  rintro ⟨h, -⟩
  have h' : riemannZeta 0 = 0 := h
  rw [riemannZeta_zero] at h'
  norm_num at h'

/-- Coeficiente exato no eixo puro: em `w = 2` ele é `ζ(2) − ζ(0) = π²/6 + 1/2`, positivo. -/
theorem Idem.eixo_puro_dois :
    Idem.aplica riemannZeta ⟨0, 2⟩ = ⟨-1 / 2, (Real.pi : ℂ) ^ 2 / 6 + 1 / 2⟩ := by
  refine Idem.ext ?_ ?_
  · show riemannZeta 0 = -1 / 2
    exact riemannZeta_zero
  · show riemannZeta (0 + 2) - riemannZeta 0 = (Real.pi : ℂ) ^ 2 / 6 + 1 / 2
    rw [zero_add, riemannZeta_two, riemannZeta_zero]
    ring

/-! ## 3. `ℂ⁴`: o número que carrega o quarteto -/

/-- `Q(s) = (ζ s, ζ(1 − s), ζ s̄, ζ(1 − s̄))` em `ℂ⁴ = ℂ × ℂ × ℂ × ℂ` (produto componente a componente). -/
noncomputable def Q (s : ℂ) : ℂ × ℂ × ℂ × ℂ :=
  (riemannZeta s, riemannZeta (tensao s), riemannZeta (espelho s), riemannZeta (torcao s))

/-- Os idempotentes de `ℂ⁴`: `e₁² = e₁` e `e₁·e₂ = 0`. -/
theorem C4_idempotentes :
    ((1, 0, 0, 0) : ℂ × ℂ × ℂ × ℂ) * (1, 0, 0, 0) = (1, 0, 0, 0) ∧
      ((1, 0, 0, 0) : ℂ × ℂ × ℂ × ℂ) * (0, 1, 0, 0) = 0 := by
  constructor <;> simp

/-- Na faixa, `Q(s) = 0 ⟺ ζ(s) = 0`: as outras três coordenadas são obrigadas pela simetria. -/
theorem Q_eq_zero_iff {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) : Q s = 0 ↔ riemannZeta s = 0 := by
  constructor
  · intro h
    simp only [Q, Prod.mk_eq_zero] at h
    exact h.1
  · intro hz
    have hs : s ∈ Z := ⟨hz, h0, h1⟩
    obtain ⟨a, -, -⟩ := tensao_mem_Z hs
    obtain ⟨b, -, -⟩ := espelho_mem_Z hs
    obtain ⟨c, -, -⟩ := torcao_mem_Z hs
    simp only [Q, Prod.mk_eq_zero]
    exact ⟨hz, a, b, c⟩

/-- A "RH-Quarteto" proposta: `Re s ≠ 1/2 ⟹ Q(s) ≠ 0`. -/
def RHQuarteto : Prop := ∀ s : ℂ, s.re ≠ 1 / 2 → Q s ≠ 0

/-- **A RH-Quarteto é RH**, sem restrição de faixa: fora da faixa `Q ≠ 0` já é teorema (Mathlib). -/
theorem rhQuarteto_iff : RHQuarteto ↔ RHFaixa := by
  constructor
  · intro h s hs
    by_contra hre
    obtain ⟨hz, h0, h1⟩ := hs
    exact h s hre ((Q_eq_zero_iff h0 h1).mpr hz)
  · intro h s hre hQ
    simp only [Q, Prod.mk_eq_zero] at hQ
    obtain ⟨hz, ht, -, -⟩ := hQ
    by_cases h1 : 1 ≤ s.re
    · exact riemannZeta_ne_zero_of_one_le_re h1 hz
    by_cases h0 : s.re ≤ 0
    · have : 1 ≤ (tensao s).re := by rw [re_tensao]; linarith
      exact riemannZeta_ne_zero_of_one_le_re this ht
    push_neg at h1 h0
    exact hre (h s ⟨hz, h0, h1⟩)

/-! ## 4. `Dual`: a "RH-Dual" é a conjectura dos zeros simples -/

def RHDual : Prop := ∀ x : Dual, Dual.aplica riemannZeta x = ⟨0, 0⟩ → x.w = 0

def ZerosSimples : Prop := ∀ s : ℂ, riemannZeta s = 0 → deriv riemannZeta s ≠ 0

theorem rhDual_iff_zerosSimples : RHDual ↔ ZerosSimples := by
  constructor
  · intro h s hz hd
    have hw := h ⟨s, 1⟩ ((Dual.aplica_eq_zero riemannZeta ⟨s, 1⟩).mpr ⟨hz, Or.inl hd⟩)
    simp at hw
  · intro h x hx
    obtain ⟨hz, hd | hw⟩ := (Dual.aplica_eq_zero riemannZeta x).mp hx
    · exact absurd hd (h _ hz)
    · exact hw

end EixoRiemann

#print axioms EixoRiemann.orbitas_iguais_ou_disjuntas
#print axioms EixoRiemann.orbita_card
#print axioms EixoRiemann.orbita_metade_de_cima
#print axioms EixoRiemann.zeros_fora_em_quartetos
#print axioms EixoRiemann.Idem.trivial_carrega_trivial
#print axioms EixoRiemann.rhIdemProposta_implica_sem_zeros
#print axioms EixoRiemann.rhIdem_iff
#print axioms EixoRiemann.Idem.eixo_puro_nunca_zero
#print axioms EixoRiemann.Idem.eixo_puro_dois
#print axioms EixoRiemann.C4_idempotentes
#print axioms EixoRiemann.Q_eq_zero_iff
#print axioms EixoRiemann.rhQuarteto_iff
#print axioms EixoRiemann.rhDual_iff_zerosSimples
