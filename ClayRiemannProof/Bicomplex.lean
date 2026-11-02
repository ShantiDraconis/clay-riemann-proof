import ClayRiemannProof.Main

/-!
# O segundo universo `j`: números bicomplexos e os zeros de ζ

Um bicomplexo é `w = z₁ + j z₂`, com `z₁, z₂ ∈ ℂ`, `j² = −1` e `j` comutando com `i`. Então `k = i j`
satisfaz `k² = +1`, e `(1 + k)(1 − k) = 0` com os dois fatores não nulos: há **divisores de zero**
(`k_sq`, `divisor_de_zero`). Isso é o "segundo universo" da conversa, agora como álgebra exata.

O fato decisivo é a **decomposição idempotente**: `w ↦ (w₊, w₋) = (z₁ − i z₂, z₁ + i z₂)` respeita soma e
produto (`plus_mul`, `minus_mul`) e é bijetiva (`ofPair`). Um bicomplexo é zero exatamente quando as duas
coordenadas são zero, e é divisor de zero exatamente quando **uma** delas é zero.

A extensão bicomplexa de ζ é `ζ_bc(w) = (ζ(w₊), ζ(w₋))` nas coordenadas idempotentes (`zetaBC`); em `ℂ`
(`z₂ = 0`) ela é a própria ζ (`zetaBC_ofComplex`). Daí, **sem hipóteses**:

* `zetaBC_eq_zero_iff`: `ζ_bc(w) = 0 ⟺ ζ(w₊) = 0 ∧ ζ(w₋) = 0` — todo zero bicomplexo é um **par de zeros
  complexos**;
* `zetaBC_divisor_iff`: o valor `ζ_bc(w)` é divisor de zero ⟺ ζ se anula em **uma** das coordenadas — o zero
  "escondido num universo" é um zero complexo comum;
* **`target_iff_RHbc`**: o enunciado do Clay ⟺ a RH bicomplexa (todo zero bicomplexo não trivial tem as duas
  coordenadas na reta crítica).

Ou seja: o segundo universo `j` **não cria nem esconde** zeros de ζ. O deslocamento `σ_ef = σ − b` também
existe dentro de `ℂ`: uma altura complexa `t = a + i b` dá `Re(σ + i t) = σ − b` (`re_altura_complexa`), e
`ζ(σ + i t)` é só ζ noutro ponto de `ℂ`.

Isto é uma reformulação exata, não progresso em RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Bicomplex

open Complex

/-- Bicomplexo `z₁ + j z₂`. -/
@[ext] structure BC where
  /-- coordenada `1` -/
  c1 : ℂ
  /-- coordenada `j` -/
  c2 : ℂ

instance : Zero BC := ⟨⟨0, 0⟩⟩
instance : One BC := ⟨⟨1, 0⟩⟩
instance : Add BC := ⟨fun a b => ⟨a.c1 + b.c1, a.c2 + b.c2⟩⟩
instance : Neg BC := ⟨fun a => ⟨-a.c1, -a.c2⟩⟩
instance : Sub BC := ⟨fun a b => ⟨a.c1 - b.c1, a.c2 - b.c2⟩⟩
/-- `(z₁ + j z₂)(w₁ + j w₂) = (z₁w₁ − z₂w₂) + j(z₁w₂ + z₂w₁)`, pois `j² = −1`. -/
instance : Mul BC := ⟨fun a b => ⟨a.c1 * b.c1 - a.c2 * b.c2, a.c1 * b.c2 + a.c2 * b.c1⟩⟩

@[simp] theorem zero_c1 : (0 : BC).c1 = 0 := rfl
@[simp] theorem zero_c2 : (0 : BC).c2 = 0 := rfl
@[simp] theorem one_c1 : (1 : BC).c1 = 1 := rfl
@[simp] theorem one_c2 : (1 : BC).c2 = 0 := rfl
@[simp] theorem add_c1 (a b : BC) : (a + b).c1 = a.c1 + b.c1 := rfl
@[simp] theorem add_c2 (a b : BC) : (a + b).c2 = a.c2 + b.c2 := rfl
@[simp] theorem neg_c1 (a : BC) : (-a).c1 = -a.c1 := rfl
@[simp] theorem neg_c2 (a : BC) : (-a).c2 = -a.c2 := rfl
@[simp] theorem sub_c1 (a b : BC) : (a - b).c1 = a.c1 - b.c1 := rfl
@[simp] theorem sub_c2 (a b : BC) : (a - b).c2 = a.c2 - b.c2 := rfl
@[simp] theorem mul_c1 (a b : BC) : (a * b).c1 = a.c1 * b.c1 - a.c2 * b.c2 := rfl
@[simp] theorem mul_c2 (a b : BC) : (a * b).c2 = a.c1 * b.c2 + a.c2 * b.c1 := rfl

/-- O segundo imaginário `j`. -/
def j : BC := ⟨0, 1⟩
/-- O imaginário `i` de `ℂ`, visto em `BC`. -/
def iBC : BC := ⟨I, 0⟩
/-- `k = i j`. -/
def k : BC := iBC * j

theorem j_sq : j * j = -1 := by ext <;> simp [j]
theorem i_sq : iBC * iBC = -1 := by ext <;> simp [iBC]
theorem k_eq : k = ⟨0, I⟩ := by ext <;> simp [k, iBC, j]
/-- **`k² = +1`**. -/
theorem k_sq : k * k = 1 := by rw [k_eq]; ext <;> simp

/-- **Divisores de zero**: `(1 + k)(1 − k) = 0` com `1 + k ≠ 0` e `1 − k ≠ 0`. -/
theorem divisor_de_zero : (1 + k) * (1 - k) = 0 ∧ (1 + k) ≠ 0 ∧ (1 - k) ≠ 0 := by
  rw [k_eq]
  refine ⟨?_, ?_, ?_⟩
  · ext <;> simp
  · intro h; have := congrArg BC.c1 h; simp at this
  · intro h; have := congrArg BC.c1 h; simp at this

/-! ## Coordenadas idempotentes -/

/-- `w₊ = z₁ − i z₂`. -/
def plus (w : BC) : ℂ := w.c1 - I * w.c2
/-- `w₋ = z₁ + i z₂`. -/
def minus (w : BC) : ℂ := w.c1 + I * w.c2

theorem plus_add (a b : BC) : plus (a + b) = plus a + plus b := by simp [plus]; ring
theorem minus_add (a b : BC) : minus (a + b) = minus a + minus b := by simp [minus]; ring
theorem plus_mul (a b : BC) : plus (a * b) = plus a * plus b := by
  simp only [plus, mul_c1, mul_c2]; ring_nf; rw [I_sq]; ring
theorem minus_mul (a b : BC) : minus (a * b) = minus a * minus b := by
  simp only [minus, mul_c1, mul_c2]; ring_nf; rw [I_sq]; ring

/-- O bicomplexo com coordenadas idempotentes `(p, m)`. -/
noncomputable def ofPair (p m : ℂ) : BC := ⟨(p + m) / 2, (m - p) / (2 * I)⟩

@[simp] theorem plus_ofPair (p m : ℂ) : plus (ofPair p m) = p := by
  simp only [plus, ofPair]; field_simp; ring
@[simp] theorem minus_ofPair (p m : ℂ) : minus (ofPair p m) = m := by
  simp only [minus, ofPair]; field_simp; ring

/-- As coordenadas idempotentes determinam o bicomplexo. -/
theorem eq_iff_plus_minus {a b : BC} : a = b ↔ plus a = plus b ∧ minus a = minus b := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    simp only [plus, minus] at h1 h2
    have hc1 : a.c1 = b.c1 := by linear_combination (h1 + h2) / 2
    have hc2 : a.c2 = b.c2 := by
      have : I * (a.c2 - b.c2) = 0 := by linear_combination (h2 - h1) / 2
      simpa [sub_eq_zero, I_ne_zero] using this
    ext <;> assumption

theorem eq_zero_iff (w : BC) : w = 0 ↔ plus w = 0 ∧ minus w = 0 := by
  rw [eq_iff_plus_minus]; simp [plus, minus]

/-- `w` é divisor de zero (existe `v ≠ 0` com `w v = 0`) ⟺ uma coordenada idempotente de `w` é zero. -/
theorem divisor_iff (w : BC) : (∃ v : BC, v ≠ 0 ∧ w * v = 0) ↔ plus w = 0 ∨ minus w = 0 := by
  constructor
  · rintro ⟨v, hv, hwv⟩
    rw [eq_zero_iff, plus_mul, minus_mul] at hwv
    by_contra h
    obtain ⟨h1, h2⟩ := not_or.mp h
    apply hv
    rw [eq_zero_iff]
    exact ⟨(mul_eq_zero.mp hwv.1).resolve_left h1, (mul_eq_zero.mp hwv.2).resolve_left h2⟩
  · rintro (h | h)
    · refine ⟨ofPair 1 0, ?_, ?_⟩
      · intro h0; have := congrArg plus h0; rw [plus_ofPair] at this; simp [plus] at this
      · rw [eq_zero_iff, plus_mul, minus_mul]; simp [h]
    · refine ⟨ofPair 0 1, ?_, ?_⟩
      · intro h0; have := congrArg minus h0; rw [minus_ofPair] at this; simp [minus] at this
      · rw [eq_zero_iff, plus_mul, minus_mul]; simp [h]

/-! ## A extensão bicomplexa de ζ -/

/-- `ζ_bc(w) = (ζ(w₊), ζ(w₋))` nas coordenadas idempotentes. -/
noncomputable def zetaBC (w : BC) : BC := ofPair (riemannZeta (plus w)) (riemannZeta (minus w))

/-- Em `ℂ` (coordenada `j` nula), `ζ_bc` é a ζ de Riemann. -/
theorem zetaBC_ofComplex (s : ℂ) : zetaBC ⟨s, 0⟩ = ⟨riemannZeta s, 0⟩ := by
  have hp : plus ⟨s, 0⟩ = s := by simp [plus]
  have hm : minus ⟨s, 0⟩ = s := by simp [minus]
  rw [eq_iff_plus_minus, zetaBC, plus_ofPair, minus_ofPair, hp, hm]
  exact ⟨by simp [plus], by simp [minus]⟩

/-- **Todo zero bicomplexo é um par de zeros complexos.** -/
theorem zetaBC_eq_zero_iff (w : BC) :
    zetaBC w = 0 ↔ riemannZeta (plus w) = 0 ∧ riemannZeta (minus w) = 0 := by
  rw [eq_zero_iff, zetaBC, plus_ofPair, minus_ofPair]

/-- **O zero "escondido num universo" é um zero complexo comum**: `ζ_bc(w)` é divisor de zero ⟺ ζ se anula
em uma das coordenadas idempotentes. -/
theorem zetaBC_divisor_iff (w : BC) :
    (∃ v : BC, v ≠ 0 ∧ zetaBC w * v = 0) ↔ riemannZeta (plus w) = 0 ∨ riemannZeta (minus w) = 0 := by
  rw [divisor_iff, zetaBC, plus_ofPair, minus_ofPair]

/-- Coordenada não trivial: não é zero trivial nem o polo. -/
def NaoTrivial (s : ℂ) : Prop := (¬ ∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1

/-- **RH bicomplexa**: todo zero bicomplexo com as duas coordenadas não triviais tem as duas na reta. -/
def RHbc : Prop :=
  ∀ w : BC, zetaBC w = 0 → NaoTrivial (plus w) → NaoTrivial (minus w) →
    (plus w).re = 1 / 2 ∧ (minus w).re = 1 / 2

/-- **O segundo universo não muda o problema**: Clay ⟺ RH bicomplexa. -/
theorem target_iff_RHbc : Target ↔ RHbc := by
  constructor
  · intro h w hz hp hm
    rw [zetaBC_eq_zero_iff] at hz
    exact ⟨h _ hz.1 hp.1 hp.2, h _ hz.2 hm.1 hm.2⟩
  · intro h s hz ht hs1
    have hp : plus ⟨s, 0⟩ = s := by simp [plus]
    have hm : minus ⟨s, 0⟩ = s := by simp [minus]
    have hz' : zetaBC ⟨s, 0⟩ = 0 := by rw [zetaBC_eq_zero_iff, hp, hm]; exact ⟨hz, hz⟩
    have := h ⟨s, 0⟩ hz' (by rw [hp]; exact ⟨ht, hs1⟩) (by rw [hm]; exact ⟨ht, hs1⟩)
    rw [hp] at this
    exact this.1

/-! ## O deslocamento `σ_ef = σ − b` dentro de `ℂ` -/

/-- Altura real: a parte imaginária não muda a parte real. -/
theorem re_altura_real (σ t : ℝ) : ((σ : ℂ) + I * t).re = σ := by simp

/-- **Altura complexa `t = a + i b`**: `Re(σ + i t) = σ − b`. O deslocamento da conversa acontece em `ℂ`
mesmo, sem segundo universo; `ζ(σ + i t)` é ζ no ponto `(σ − b) + i a`. -/
theorem re_altura_complexa (σ a b : ℝ) : ((σ : ℂ) + I * (a + I * b)).re = σ - b := by
  simp [mul_add, ← mul_assoc]; ring

end ClayRiemannProof.Bicomplex
