import ClayRiemannProof.EixoRiemann.Quarteto

/-!
# Pontes no eixo Riemann e o quarteto como operador

Uma **ponte** é `N = z₁ + δ·e` em `Idem` com `ζ(N) = (0, 0)`, ou seja, `z₁` e `z₂ = z₁ + δ` zeros de ζ
(`Idem.aplica_eq_zero`). As pontes são exatamente os pares ordenados de zeros.

* `Idem.avalia_mul_iff`: `e ↦ c` respeita o produto de `Idem` ⟺ `c = 0` ou `c = 1`. A ponte tem só as duas
  pontas: `e = 0,25`, `e = 0,5` não são pontos de `Idem`, são pontos do segmento em `ℂ`, fora da álgebra.
* `Q_espelho`, `Q_tensao`, `Q_torcao`: **o quarteto como operador**. O grupo de Klein age em `ℂ⁴` permutando
  coordenadas, e `Q(s) = (ζ s, ζ(1 − s), ζ s̄, ζ(1 − s̄))` comuta com essa ação.
* `ponte_horizontal_do_quarteto`: um zero fora da reta `ρ` dá a ponte `ρ → 1 − ρ̄` com `δ = 1 − 2·Re ρ`,
  **real e não nulo**. Um zero na reta só tem pontes com `Re δ = 0` dentro da faixa.
* `rh_iff_sem_ponte_horizontal`: RH ⟺ não existe ponte horizontal (`δ` real, `δ ≠ 0`) com as duas pontas
  zeros na faixa. É a forma exata da proposta "zero fora = quarteto como operador + pontes". É uma
  equivalência: localiza RH, não prova.
-/

open ClayRiemannProof.Zeta.Symmetry

namespace EixoRiemann

/-- Avaliar `e` em `c`: `z + w·e ↦ z + c·w`. -/
def Idem.avalia (c : ℂ) (x : Idem) : ℂ := x.z + c * x.w

/-- **A ponte só tem duas pontas.** -/
theorem Idem.avalia_mul_iff (c : ℂ) :
    (∀ x y : Idem, Idem.avalia c (x * y) = Idem.avalia c x * Idem.avalia c y) ↔ c = 0 ∨ c = 1 := by
  constructor
  · intro h
    have h1 := h ⟨0, 1⟩ ⟨0, 1⟩
    simp only [Idem.avalia, Idem.mul_z, Idem.mul_w] at h1
    have h2 : c * (c - 1) = 0 := by linear_combination -h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact Or.inl h3
    · exact Or.inr (sub_eq_zero.mp h3)
  · rintro (rfl | rfl) x y
    · simp only [Idem.avalia, Idem.mul_z, Idem.mul_w]
      ring
    · simp only [Idem.avalia, Idem.mul_z, Idem.mul_w]
      ring

/-! ## O quarteto como operador em `ℂ⁴` -/

theorem Q_espelho (s : ℂ) :
    Q (espelho s) = ((Q s).2.2.1, (Q s).2.2.2, (Q s).1, (Q s).2.1) := by
  simp only [Q, ten_esp, espelho_espelho, tor_esp]

theorem Q_tensao (s : ℂ) :
    Q (tensao s) = ((Q s).2.1, (Q s).1, (Q s).2.2.2, (Q s).2.2.1) := by
  simp only [Q, tensao_tensao, esp_ten, tor_ten]

theorem Q_torcao (s : ℂ) :
    Q (torcao s) = ((Q s).2.2.2, (Q s).2.2.1, (Q s).2.1, (Q s).1) := by
  simp only [Q, torcao_torcao, esp_tor, ten_tor]

/-! ## Pontes horizontais -/

theorem soma_real_eq_torcao (ρ : ℂ) : ρ + ((1 - 2 * ρ.re : ℝ) : ℂ) = torcao ρ := by
  apply Complex.ext
  · rw [re_torcao, Complex.add_re, Complex.ofReal_re]
    ring
  · rw [im_tor, Complex.add_im, Complex.ofReal_im, add_zero]

/-- Um zero na faixa dá a ponte `ρ → 1 − ρ̄`, com `δ = 1 − 2·Re ρ` real. Fora da reta, `δ ≠ 0`. -/
theorem ponte_horizontal_do_quarteto {ρ : ℂ} (hρ : ρ ∈ Z) :
    Idem.aplica riemannZeta ⟨ρ, ((1 - 2 * ρ.re : ℝ) : ℂ)⟩ = ⟨0, 0⟩ := by
  rw [Idem.aplica_eq_zero]
  obtain ⟨ht, -, -⟩ := torcao_mem_Z hρ
  obtain ⟨hz, -, -⟩ := hρ
  refine ⟨hz, ?_⟩
  show riemannZeta (ρ + ((1 - 2 * ρ.re : ℝ) : ℂ)) = 0
  rw [soma_real_eq_torcao]
  exact ht

/-- Ponte horizontal: `δ` real e não nulo, as duas pontas zeros de ζ na faixa. -/
def PonteHorizontal : Prop := ∃ s : ℂ, ∃ r : ℝ, r ≠ 0 ∧ s ∈ Z ∧ s + (r : ℂ) ∈ Z

/-- **RH ⟺ nenhuma ponte horizontal segura.** -/
theorem rh_iff_sem_ponte_horizontal : RHFaixa ↔ ¬ PonteHorizontal := by
  unfold PonteHorizontal
  constructor
  · rintro h ⟨s, r, hr, hs, hsr⟩
    have a := h s hs
    have b := h _ hsr
    rw [Complex.add_re, Complex.ofReal_re] at b
    exact hr (by linarith)
  · intro h ρ hρ
    by_contra hre
    apply h
    refine ⟨ρ, 1 - 2 * ρ.re, ?_, hρ, ?_⟩
    · intro h0
      apply hre
      linarith
    · rw [soma_real_eq_torcao]
      exact torcao_mem_Z hρ

end EixoRiemann

#print axioms EixoRiemann.Idem.avalia_mul_iff
#print axioms EixoRiemann.Q_espelho
#print axioms EixoRiemann.Q_tensao
#print axioms EixoRiemann.Q_torcao
#print axioms EixoRiemann.ponte_horizontal_do_quarteto
#print axioms EixoRiemann.rh_iff_sem_ponte_horizontal
