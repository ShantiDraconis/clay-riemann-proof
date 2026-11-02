import ClayRiemannProof.Bridges

/-!
# O mesmo comportamento em outras áreas: o quarteto, o círculo e as duas saídas da linha

Este arquivo põe no kernel a parte **matemática** do catálogo de análogos: o que é igual entre a RH e os outros
sistemas com zeros "fora da linha", e o que é diferente.

* **Lei abstrata do quarteto** (`quarteto_abstrato`): toda `f` com `f(−w) = f(w)` e `f(w̄) = conj f(w)` tem os zeros
  em quartetos `w, −w, w̄, −w̄`. A zeta completada na coordenada `w = s − ½` é uma instância
  (`xi_simetrica`), e também o são a partição da QCD em `μ̂ = μ_B/T` e os polinômios característicos pares de
  matrizes hamiltonianas reais. **A simetria não segura os zeros na linha** (`simetria_nao_basta_abstrata`).
* **Lei universal do círculo** (`ihara_ramanujan`): para `λ, q` reais, `q > 0`, as raízes de `1 − λu + qu² = 0`
  satisfazem `q|u|² = 1 ⟺ λ² ≤ 4q`. Ela é a "RH" da função zeta de Ihara de um grafo `(q+1)`-regular para um autovalor
  `λ` da adjacência (cota de Ramanujan). Com `q = 1` ela dá o teorema do círculo de Lee–Yang para dois spins:
  círculo ⟺ ferromagnético (`lee_yang_ferro`). As raízes formam o quarteto `u, ū, 1/(qu), 1/(qū)`
  (`ihara_quarteto`), e `u = q^{−s}` leva o círculo à reta `Re s = ½` (`circulo_iff_reta`). Fora do círculo, as
  raízes são **reais** (`ihara_fora_real`).
* **As duas saídas da linha**: num sistema autoadjunto, com `λ = s(1 − s)` real, um zero só pode sair da reta
  **pelo eixo real** (`lam_real_iff`). São os autovalores excepcionais de Selberg, os grafos não Ramanujan e o
  Lee–Yang antiferromagnético, com a conjectura `λ ≥ ¼` de Selberg como RH (`linha_iff_quarto`). Um quarteto complexo
  genuíno (`b ≠ 0`, `t ≠ 0`) exige perder a autoadjunção. São os casos de Davenport–Heilbronn, Epstein, simetria PT
  quebrada e colisão de Krein de sinais opostos.
* **Para ζ a saída real está fechada no kernel**: `ζ(σ) < 0` em `(0, 1)` (`Zeta.Symmetry.zeta_real_neg`). Por isso
  `selberg_polya` é mais forte que o caso de Selberg: um operador simétrico com todo `λ(ρ)` como autovalor já
  implica o enunciado do Clay. Nenhum tal operador é conhecido.

Nada aqui prova RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Analogs

open Complex ComplexConjugate ClayRiemannProof.Zeta.Symmetry ClayRiemannProof.Bridges

/-! ## 1. A lei abstrata do quarteto -/

/-- As duas simetrias da RH na coordenada `w = s − ½`; as mesmas da QCD em `μ̂` e dos espectros hamiltonianos. -/
def Simetrica (f : ℂ → ℂ) : Prop := (∀ w, f (-w) = f w) ∧ ∀ w, f (conj w) = conj (f w)

/-- **Lei do quarteto**: os zeros de uma função simétrica vêm em `w, −w, w̄, −w̄`. -/
theorem quarteto_abstrato {f : ℂ → ℂ} (hf : Simetrica f) {w : ℂ} (h : f w = 0) :
    f (-w) = 0 ∧ f (conj w) = 0 ∧ f (-conj w) = 0 :=
  ⟨by rw [hf.1, h], by rw [hf.2, h, map_zero], by rw [hf.1, hf.2, h, map_zero]⟩

/-- A zeta completada na coordenada `w = s − ½`. -/
noncomputable def xiW (w : ℂ) : ℂ := completedRiemannZeta (1 / 2 + w)

/-- **A zeta completada é uma instância da lei do quarteto** (equação funcional e conjugação da Mathlib). -/
theorem xi_simetrica : Simetrica xiW := by
  constructor
  · intro w
    unfold xiW
    rw [show (1 / 2 : ℂ) + -w = 1 - (1 / 2 + w) by ring, completedRiemannZeta_one_sub]
  · intro w
    unfold xiW
    rw [show (1 / 2 : ℂ) + conj w = conj (1 / 2 + w) by rw [map_add, map_div₀, map_one, map_ofNat],
      completedRiemannZeta_conj]

/-- Polinômio com o quarteto `±z, ±z̄`. -/
noncomputable def quartetoPoly (z w : ℂ) : ℂ := (w - z) * (w + z) * (w - conj z) * (w + conj z)

theorem quartetoPoly_simetrica (z : ℂ) : Simetrica (quartetoPoly z) := by
  constructor
  · intro w
    unfold quartetoPoly
    ring
  · intro w
    unfold quartetoPoly
    simp only [map_mul, map_sub, map_add, conj_conj]
    ring

/-- **A simetria não segura os zeros na linha `Re w = 0`**: o quarteto `±¼ ± i`. -/
theorem simetria_nao_basta_abstrata :
    ∃ f : ℂ → ℂ, Simetrica f ∧ f (1 / 4 + I) = 0 ∧ (1 / 4 + I : ℂ).re ≠ 0 := by
  refine ⟨quartetoPoly (1 / 4 + I), quartetoPoly_simetrica _, by unfold quartetoPoly; ring, ?_⟩
  norm_num

/-! ## 2. A lei universal do círculo (Ihara–Ramanujan, Lee–Yang) -/

/-- Partes real e imaginária de `1 − λu + qu² = 0`. -/
theorem partes {q l : ℝ} {u : ℂ} (hu : 1 - l * u + q * u ^ 2 = 0) :
    1 - l * u.re + q * (u.re ^ 2 - u.im ^ 2) = 0 ∧ u.im * (2 * q * u.re - l) = 0 := by
  have hre := congrArg Complex.re hu
  have him := congrArg Complex.im hu
  simp [pow_two] at hre him
  constructor
  · linarith
  · linarith

/-- **Lei universal do círculo**: `q|u|² = 1 ⟺ λ² ≤ 4q`. Para Ihara é a cota de Ramanujan `|λ| ≤ 2√q`. -/
theorem ihara_ramanujan {q l : ℝ} (hq : 0 < q) {u : ℂ} (hu : 1 - l * u + q * u ^ 2 = 0) :
    q * normSq u = 1 ↔ l ^ 2 ≤ 4 * q := by
  obtain ⟨hre, him⟩ := partes hu
  rw [normSq_apply]
  set x := u.re
  set y := u.im
  rcases mul_eq_zero.mp him with hy | hx
  · rw [hy] at hre ⊢
    constructor
    · intro h
      have hlx : l * x = 2 := by nlinarith
      have : l ^ 2 * (q * x ^ 2) = 4 * q := by
        have e : l ^ 2 * (q * x ^ 2) = q * (l * x) ^ 2 := by ring
        rw [e, hlx]; ring
      nlinarith
    · intro h
      have hsq : (2 * q * x - l) ^ 2 = l ^ 2 - 4 * q := by nlinarith
      have h0 : (2 * q * x - l) ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
      have hl : l = 2 * q * x := by nlinarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp h0]
      rw [hl] at hre
      nlinarith
  · have hl : l = 2 * q * x := by linarith
    rw [hl] at hre ⊢
    constructor
    · intro h
      have e : (2 * q * x) ^ 2 = 4 * q - 4 * q ^ 2 * y ^ 2 := by linear_combination (4 * q) * h
      have : 0 ≤ q ^ 2 * y ^ 2 := by positivity
      rw [e]
      linarith
    · intro _
      nlinarith

/-- Fora do círculo, as raízes são reais. -/
theorem ihara_fora_real {q l : ℝ} (hq : 0 < q) {u : ℂ} (hu : 1 - l * u + q * u ^ 2 = 0)
    (h : 4 * q < l ^ 2) : u.im = 0 := by
  obtain ⟨hre, him⟩ := partes hu
  rcases mul_eq_zero.mp him with hy | hx
  · exact hy
  · exfalso
    have hl : l = 2 * q * u.re := by linarith
    rw [hl] at hre h
    have e : (2 * q * u.re) ^ 2 = 4 * q - 4 * q ^ 2 * u.im ^ 2 := by linear_combination (-4 * q) * hre
    have : 0 ≤ q ^ 2 * u.im ^ 2 := by positivity
    linarith

/-- **O quarteto de Ihara**: com `u` também são raízes `ū` e `1/(qu)` (a equação funcional `s ↦ 1 − s`). -/
theorem ihara_quarteto {q l : ℝ} (hq : 0 < q) {u : ℂ} (hu : 1 - l * u + q * u ^ 2 = 0) :
    (1 - l * conj u + q * conj u ^ 2 = 0) ∧ (1 - l * (q * u)⁻¹ + q * ((q * u)⁻¹) ^ 2 = 0) := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  constructor
  · have := congrArg conj hu
    simpa [map_sub, map_add, map_mul, map_pow] using this
  · field_simp
    linear_combination hu

/-- **Do círculo para a reta**: com `u = q^{−s}` (`L = log q ≠ 0`), `q|u|² = 1 ⟺ Re s = ½`. -/
theorem circulo_iff_reta {L : ℝ} (hL : L ≠ 0) (s : ℂ) :
    Real.exp L * normSq (cexp (-(L : ℂ) * s)) = 1 ↔ s.re = 1 / 2 := by
  rw [← Complex.sq_norm, Complex.norm_exp, ← Real.exp_nat_mul, ← Real.exp_add, Real.exp_eq_one_iff]
  simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, Nat.cast_ofNat]
  constructor
  · intro h
    have : L * (1 - 2 * s.re) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd h1 hL
    · linarith
  · intro h
    rw [h]
    ring

/-- **Lee–Yang, dois spins**: `z² + 2az + 1 = 0` com `a > 0`; `|z| = 1 ⟺ a ≤ 1`. -/
theorem lee_yang_dois_spins {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z ^ 2 + 2 * a * z + 1 = 0) :
    normSq z = 1 ↔ a ≤ 1 := by
  have hu : 1 - ((-2 * a : ℝ) : ℂ) * z + ((1 : ℝ) : ℂ) * z ^ 2 = 0 := by
    push_cast
    linear_combination hz
  have := ihara_ramanujan (q := 1) (l := -2 * a) one_pos hu
  rw [one_mul] at this
  rw [this]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- **Lee–Yang, dois spins, com a constante de acoplamento**: `a = e^{−2βJ}`, `β > 0`; no círculo ⟺
ferromagnético (`J ≥ 0`). -/
theorem lee_yang_ferro {β J : ℝ} (hβ : 0 < β) {z : ℂ}
    (hz : z ^ 2 + 2 * Real.exp (-2 * β * J) * z + 1 = 0) : normSq z = 1 ↔ 0 ≤ J := by
  rw [lee_yang_dois_spins (Real.exp_pos _) hz, Real.exp_le_one_iff]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-! ## 3. As duas saídas da linha e a de ζ -/

/-- **Com `λ` real, a única saída da reta é o eixo real.** -/
theorem lam_real_iff (s : ℂ) : (lam s).im = 0 ↔ s.re = 1 / 2 ∨ s.im = 0 := by
  rw [lam_im]
  constructor
  · intro h
    have : (s.re - 1 / 2) * s.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · left; linarith
    · right; exact h1
  · rintro (h | h)
    · rw [h]; ring
    · rw [h]; ring

/-- **A conjectura `λ ≥ ¼` de Selberg como RH**: com `λ` real, `s` está na reta ⟺ `λ ≥ ¼`. -/
theorem linha_iff_quarto {s : ℂ} (h : (lam s).im = 0) : s.re = 1 / 2 ↔ 1 / 4 ≤ (lam s).re := by
  rw [lam_re]
  constructor
  · intro hs
    rw [hs]
    nlinarith [sq_nonneg s.im]
  · intro hq
    rcases (lam_real_iff s).mp h with h1 | h1
    · exact h1
    · rw [h1] at hq
      have : (s.re - 1 / 2) ^ 2 = 0 := le_antisymm (by nlinarith) (sq_nonneg _)
      have := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp this
      linarith

/-- **Autovalor excepcional**: `s = σ ∈ (½, 1)` real dá `λ` real em `(0, ¼)`. É o zero fora da reta que um
problema espectral autoadjunto ainda permite (Selberg; grafos não Ramanujan). -/
theorem excepcional {σ : ℝ} (h1 : 1 / 2 < σ) (h2 : σ < 1) :
    (lam σ).im = 0 ∧ 0 < (lam σ).re ∧ (lam σ).re < 1 / 4 := by
  refine ⟨by rw [lam_im]; simp, ?_, ?_⟩
  · rw [lam_re]; simp; nlinarith
  · rw [lam_re]; simp; nlinarith

/-- **Para ζ a saída real está fechada**: nenhum zero não trivial é real. -/
theorem zeta_sem_saida_real {s : ℂ} (hs : s ∈ Z) : s.im ≠ 0 := im_ne_zero_of_mem_Z hs

/-- **Ponte de Selberg–Pólya**: um operador simétrico com todo `λ(ρ) = ρ(1 − ρ)` como autovalor implica o enunciado
do Clay. Em superfícies de Selberg a mesma hipótese ainda deixa os autovalores excepcionais; para ζ essa
saída está fechada por `zeta_sem_saida_real`. Nenhum tal operador é conhecido. -/
theorem selberg_polya {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (h : ∀ s ∈ Z, Module.End.HasEigenvalue T (lam s)) : Target :=
  target_iff_lam_real.mpr fun s hs => Complex.conj_eq_iff_im.mp (hT.conj_eigenvalue_eq_self (h s hs))

end ClayRiemannProof.Analogs
