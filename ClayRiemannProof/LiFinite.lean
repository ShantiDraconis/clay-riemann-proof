import ClayRiemannProof.Analogs

/-!
# O critério de Li em forma finita (Bombieri–Lagarias), sem produto de Hadamard

Para uma família **finita** de números complexos não nulos `ρ`, fechada pela simetria `ρ ↦ 1 − ρ`, os
coeficientes de Li são

    λ_n = Σ_ρ (1 − (1 − 1/ρ)^n).

* **Transformada de Cayley** `w = 1 − 1/ρ`: leva a reta `Re ρ = ½` ao círculo `|w| = 1`. A lei exata é
  `|w|²·|ρ|² = |ρ|² − (2 Re ρ − 1)` (`normSq_cayley_mul`), a mesma lei do círculo de Ihara e Lee–Yang
  (`ClayRiemannProof.Analogs`). Os casos são `|w| = 1 ⟺ Re ρ = ½` e `|w| > 1 ⟺ Re ρ < ½`.
* **Critério de Li finito** (`li_finito`): todos os `ρ` estão na reta ⟺ `Re λ_n ≥ 0` para todo `n`.
  A volta usa só somas geométricas. Se algum `ρ` sai da reta, a simetria dá um `|w| > 1`. As potências de módulo
  máximo `M > 1` dominam, e um argumento de média (`li_chave`) mostra que a parte real delas fica `≥ 1/8` para
  infinitos `n`. Então `λ_n < 0`.
* **Li em cada mundo finito** (`li_no_mundo`): se `ρ` enumera os zeros não triviais de altura `≤ Z`, então
  RH até a altura `Z` ⟺ os coeficientes de Li desses zeros são todos `≥ 0`. Com `target_iff_todos_os_mundos`, o
  enunciado do Clay é a positividade de Li em **todo** mundo finito.

O critério de Li clássico, com todos os zeros de ζ, pede o produto de Hadamard de `ξ`, que a Mathlib ainda não tem.
Esta é a forma finita, que não pede. Nada aqui prova RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.LiFinite

open Complex ComplexConjugate Finset Filter Topology ClayRiemannProof.Zeta.Symmetry

/-! ## 1. A transformada de Cayley: reta ↔ círculo -/

/-- `w(ρ) = 1 − 1/ρ`. -/
noncomputable def cayley (ρ : ℂ) : ℂ := 1 - 1 / ρ

theorem cayley_mul {ρ : ℂ} (h : ρ ≠ 0) : cayley ρ * ρ = ρ - 1 := by
  unfold cayley
  field_simp

/-- **A lei exata**: `|w|²·|ρ|² = |ρ|² − (2 Re ρ − 1)`. -/
theorem normSq_cayley_mul {ρ : ℂ} (h : ρ ≠ 0) :
    normSq (cayley ρ) * normSq ρ = normSq ρ - (2 * ρ.re - 1) := by
  rw [← normSq_mul, cayley_mul h, normSq_apply, normSq_apply]
  simp
  ring

theorem norm_sq_cayley {ρ : ℂ} (h : ρ ≠ 0) :
    ‖cayley ρ‖ ^ 2 * normSq ρ = normSq ρ - (2 * ρ.re - 1) := by
  rw [← normSq_eq_norm_sq]
  exact normSq_cayley_mul h

/-- **Reta ↔ círculo**: `|1 − 1/ρ| = 1 ⟺ Re ρ = ½`. -/
theorem norm_cayley_eq_one_iff {ρ : ℂ} (h : ρ ≠ 0) : ‖cayley ρ‖ = 1 ↔ ρ.re = 1 / 2 := by
  have hp : 0 < normSq ρ := normSq_pos.mpr h
  have e := norm_sq_cayley h
  have hn := norm_nonneg (cayley ρ)
  constructor
  · intro h1
    rw [h1] at e
    linarith
  · intro h1
    rw [h1] at e
    have h2 : (‖cayley ρ‖ ^ 2 - 1) * normSq ρ = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · nlinarith
    · linarith

/-- **Fora da reta, à esquerda**: `|1 − 1/ρ| > 1 ⟺ Re ρ < ½`. -/
theorem one_lt_norm_cayley_iff {ρ : ℂ} (h : ρ ≠ 0) : 1 < ‖cayley ρ‖ ↔ ρ.re < 1 / 2 := by
  have hp : 0 < normSq ρ := normSq_pos.mpr h
  have e := norm_sq_cayley h
  have hn := norm_nonneg (cayley ρ)
  constructor
  · intro h1
    have h2 : 1 < ‖cayley ρ‖ ^ 2 := by nlinarith
    nlinarith
  · intro h1
    by_contra h2
    have h3 := not_lt.mp h2
    have h4 : ‖cayley ρ‖ ^ 2 ≤ 1 := by nlinarith
    nlinarith

/-! ## 2. Somas geométricas no círculo -/

/-- Cota de uma soma geométrica no círculo (`0` quando `v = 1`). -/
noncomputable def bnd (v : ℂ) : ℝ := if v = 1 then 0 else 2 / ‖1 - v‖

theorem bnd_nonneg (v : ℂ) : 0 ≤ bnd v := by
  unfold bnd
  split_ifs <;> positivity

/-- `Re Σ_{m<N} v^{a+m}` vale `N` se `v = 1` e é `≥ −2/|1 − v|` se `v ≠ 1`, para `|v| = 1`. -/
theorem re_geom_ge {v : ℂ} (hv : ‖v‖ = 1) (a N : ℕ) :
    (if v = 1 then (N : ℝ) else 0) - bnd v ≤ (∑ m ∈ range N, v ^ (a + m)).re := by
  by_cases h : v = 1
  · subst h
    simp [bnd]
  · simp only [bnd, h, ↓reduceIte, zero_sub]
    have e : ∑ m ∈ range N, v ^ (a + m) = v ^ a * ((v ^ N - 1) / (v - 1)) := by
      rw [← geom_sum_eq h N, mul_sum]
      simp [pow_add]
    have hn : ‖∑ m ∈ range N, v ^ (a + m)‖ ≤ 2 / ‖1 - v‖ := by
      rw [e, norm_mul, norm_pow, hv, one_pow, one_mul, norm_div, norm_sub_rev v 1]
      gcongr
      calc ‖v ^ N - 1‖ ≤ ‖v ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hv, one_pow, norm_one]; norm_num
    have h1 := abs_re_le_norm (∑ m ∈ range N, v ^ (a + m))
    have h2 := neg_abs_le (∑ m ∈ range N, v ^ (a + m)).re
    linarith

theorem re_mul_re (a b : ℂ) : a.re * b.re = ((a * b).re + (a * conj b).re) / 2 := by
  simp [mul_re, conj_re, conj_im]

/-! ## 3. A chave: potências no círculo têm parte real `≥ 1/8` infinitas vezes -/

/-- **Lema-chave**: para uma família finita não vazia de pontos do círculo, a soma das partes reais de `u_j^n`
é `≥ 1/8` para infinitos `n`. Prova por média das somas e dos quadrados. -/
theorem li_chave {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (u : ι → ℂ)
    (hu : ∀ j ∈ s, ‖u j‖ = 1) (a : ℕ) : ∃ n, a ≤ n ∧ 1 / 8 ≤ ∑ j ∈ s, (u j ^ n).re := by
  classical
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  set k : ℝ := (s.card : ℝ) with hk
  have hk1 : 1 ≤ k := by rw [hk]; exact_mod_cast hs.card_pos
  set R : ℕ → ℝ := fun n => ∑ j ∈ s, (u j ^ n).re with hR
  have hRb : ∀ n, |R n| ≤ k := by
    intro n
    calc |R n| ≤ ∑ j ∈ s, |(u j ^ n).re| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ s, (1 : ℝ) := by
          apply sum_le_sum
          intro j hj
          calc |(u j ^ n).re| ≤ ‖u j ^ n‖ := abs_re_le_norm _
            _ = 1 := by rw [norm_pow, hu j hj, one_pow]
      _ = k := by simp [hk]
  have hpt : ∀ n, a ≤ n → R n ^ 2 ≤ 1 / 64 + k / 8 - k * R n := by
    intro n hn
    have h1 := hcon n hn
    have h2 := abs_le.mp (hRb n)
    by_cases h0 : 0 ≤ R n
    · nlinarith
    · nlinarith
  set C1 : ℝ := ∑ j ∈ s, bnd (u j) with hC1
  set C2 : ℝ := ∑ j ∈ s, ∑ l ∈ s, (bnd (u j * u l) + bnd (u j * conj (u l))) / 2 with hC2
  have hS1 : ∀ N : ℕ, -C1 ≤ ∑ m ∈ range N, R (a + m) := by
    intro N
    have e : ∑ m ∈ range N, R (a + m) = ∑ j ∈ s, (∑ m ∈ range N, u j ^ (a + m)).re := by
      simp only [hR, re_sum]
      exact sum_comm
    rw [e, hC1, ← sum_neg_distrib]
    apply sum_le_sum
    intro j hj
    have h1 := re_geom_ge (hu j hj) a N
    have h2 : (0 : ℝ) ≤ (if u j = 1 then (N : ℝ) else 0) := by split_ifs <;> positivity
    linarith
  have hS2 : ∀ N : ℕ, k * N / 2 - C2 ≤ ∑ m ∈ range N, R (a + m) ^ 2 := by
    intro N
    have e : ∀ n, R n ^ 2 =
        ∑ j ∈ s, ∑ l ∈ s, (((u j * u l) ^ n).re + ((u j * conj (u l)) ^ n).re) / 2 := by
      intro n
      simp only [hR]
      rw [sq, sum_mul_sum]
      refine sum_congr rfl fun j _ => sum_congr rfl fun l _ => ?_
      rw [re_mul_re, mul_pow, mul_pow, map_pow]
    have e2 : ∑ m ∈ range N, R (a + m) ^ 2 = ∑ j ∈ s, ∑ l ∈ s,
        ((∑ m ∈ range N, (u j * u l) ^ (a + m)).re +
          (∑ m ∈ range N, (u j * conj (u l)) ^ (a + m)).re) / 2 := by
      simp only [e]
      rw [sum_comm]
      refine sum_congr rfl fun j _ => ?_
      rw [sum_comm]
      refine sum_congr rfl fun l _ => ?_
      rw [re_sum, re_sum, ← sum_add_distrib, sum_div]
    have hterm : ∀ j ∈ s, ∀ l ∈ s,
        (if j = l then (N : ℝ) else 0) / 2 - (bnd (u j * u l) + bnd (u j * conj (u l))) / 2 ≤
          ((∑ m ∈ range N, (u j * u l) ^ (a + m)).re +
            (∑ m ∈ range N, (u j * conj (u l)) ^ (a + m)).re) / 2 := by
      intro j hj l hl
      have n1 : ‖u j * u l‖ = 1 := by rw [norm_mul, hu j hj, hu l hl, one_mul]
      have n2 : ‖u j * conj (u l)‖ = 1 := by rw [norm_mul, Complex.norm_conj, hu j hj, hu l hl, one_mul]
      have g1 := re_geom_ge n1 a N
      have g2 := re_geom_ge n2 a N
      have i1 : (0 : ℝ) ≤ (if u j * u l = 1 then (N : ℝ) else 0) := by split_ifs <;> positivity
      have i2 : (if j = l then (N : ℝ) else 0) ≤ (if u j * conj (u l) = 1 then (N : ℝ) else 0) := by
        by_cases h1 : j = l
        · subst h1
          have hc : u j * conj (u j) = 1 := by
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu j hj]
            norm_num
          simp [hc]
        · simp only [h1, ↓reduceIte]
          split_ifs <;> positivity
      linarith
    have hdiag : ∑ j ∈ s, ∑ l ∈ s, (if j = l then (N : ℝ) else 0) / 2 = k * N / 2 := by
      have h1 : ∀ j ∈ s, ∑ l ∈ s, (if j = l then (N : ℝ) else 0) / 2 = (N : ℝ) / 2 := by
        intro j hj
        rw [← sum_div, sum_ite_eq s j (fun _ => (N : ℝ))]
        simp [hj]
      rw [sum_congr rfl h1, sum_const, nsmul_eq_mul, hk]
      ring
    calc k * N / 2 - C2
        = ∑ j ∈ s, ∑ l ∈ s, ((if j = l then (N : ℝ) else 0) / 2 -
            (bnd (u j * u l) + bnd (u j * conj (u l))) / 2) := by
          simp only [sum_sub_distrib]
          rw [hdiag]
      _ ≤ _ := by
          rw [e2]
          exact sum_le_sum fun j hj => sum_le_sum fun l hl => hterm j hj l hl
  obtain ⟨N, hN⟩ := exists_nat_gt (3 * (C2 + k * C1))
  have h1 := hS1 N
  have h2 := hS2 N
  have h3 : ∑ m ∈ range N, R (a + m) ^ 2 ≤ ∑ m ∈ range N, (1 / 64 + k / 8 - k * R (a + m)) :=
    sum_le_sum fun m _ => hpt (a + m) (Nat.le_add_right a m)
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ← mul_sum] at h3
  have h4 : k * -C1 ≤ k * ∑ m ∈ range N, R (a + m) := mul_le_mul_of_nonneg_left h1 (by linarith)
  have h5 : 0 ≤ (N : ℝ) * (k - 1) := mul_nonneg (Nat.cast_nonneg N) (by linarith)
  nlinarith

/-! ## 4. O critério de Li finito -/

/-- **Coeficientes de Li** de uma família finita: `λ_n = Σ_i (1 − (1 − 1/ρ_i)^n)`. -/
noncomputable def li {ι : Type*} [Fintype ι] (ρ : ι → ℂ) (n : ℕ) : ℂ :=
  ∑ i, (1 - cayley (ρ i) ^ n)

/-- **Critério de Li finito (Bombieri–Lagarias)**: para uma família finita de não nulos fechada por
`ρ ↦ 1 − ρ`, todos na reta ⟺ `Re λ_n ≥ 0` para todo `n`. -/
theorem li_finito {ι : Type*} [Fintype ι] (ρ : ι → ℂ) (h0 : ∀ i, ρ i ≠ 0)
    (hsym : ∀ i, ∃ j, ρ j = 1 - ρ i) :
    (∀ i, (ρ i).re = 1 / 2) ↔ ∀ n : ℕ, 0 ≤ (li ρ n).re := by
  classical
  constructor
  · intro h n
    unfold li
    rw [re_sum]
    apply sum_nonneg
    intro i _
    have hw : ‖cayley (ρ i)‖ = 1 := (norm_cayley_eq_one_iff (h0 i)).mpr (h i)
    have h1 := abs_re_le_norm (cayley (ρ i) ^ n)
    rw [norm_pow, hw, one_pow] at h1
    have h2 := le_abs_self (cayley (ρ i) ^ n).re
    simp only [sub_re, one_re]
    linarith
  · intro hpos
    by_contra hne
    simp only [not_forall] at hne
    obtain ⟨i0, hi0⟩ := hne
    obtain ⟨j0, hj0⟩ : ∃ j, (ρ j).re < 1 / 2 := by
      rcases lt_or_gt_of_ne hi0 with h | h
      · exact ⟨i0, h⟩
      · obtain ⟨j, hj⟩ := hsym i0
        exact ⟨j, by rw [hj, sub_re, one_re]; linarith⟩
    set w : ι → ℂ := fun i => cayley (ρ i) with hw
    obtain ⟨imax, -, himax⟩ := exists_max_image univ (fun i => ‖w i‖) ⟨j0, mem_univ _⟩
    set M := ‖w imax‖ with hMdef
    have hM : 1 < M :=
      lt_of_lt_of_le ((one_lt_norm_cayley_iff (h0 j0)).mpr hj0) (himax j0 (mem_univ _))
    have hM0 : 0 < M := by linarith
    set s := univ.filter (fun i => ‖w i‖ = M) with hs_def
    set t := univ.filter (fun i => ¬ ‖w i‖ = M) with ht_def
    have hs : s.Nonempty := ⟨imax, by simp only [hs_def, mem_filter, mem_univ, true_and]; exact hMdef.symm⟩
    set u : ι → ℂ := fun i => w i / (M : ℂ) with hu_def
    have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
    have hu : ∀ i ∈ s, ‖u i‖ = 1 := by
      intro i hi
      simp only [hs_def, mem_filter, mem_univ, true_and] at hi
      rw [hu_def, norm_div, hi, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM0, div_self hM0.ne']
    set q : ι → ℝ := fun i => ‖w i‖ / M with hq_def
    have hq : ∀ i ∈ t, 0 ≤ q i ∧ q i < 1 := by
      intro i hi
      simp only [ht_def, mem_filter, mem_univ, true_and] at hi
      have hle : ‖w i‖ ≤ M := himax i (mem_univ _)
      refine ⟨div_nonneg (norm_nonneg _) hM0.le, ?_⟩
      rw [hq_def, div_lt_one hM0]
      exact lt_of_le_of_ne hle hi
    have T1 : Tendsto (fun n => ∑ i ∈ t, q i ^ n) atTop (𝓝 0) := by
      have := tendsto_finsetSum t fun i hi =>
        tendsto_pow_atTop_nhds_zero_of_lt_one (hq i hi).1 (hq i hi).2
      simpa using this
    have E1 := T1.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 16 by norm_num))
    have E2 := (tendsto_pow_atTop_atTop_of_one_lt hM).eventually_gt_atTop (16 * (Fintype.card ι : ℝ))
    obtain ⟨a, ha⟩ := (E1.and E2).exists_forall_of_atTop
    obtain ⟨n, hn, hkey⟩ := li_chave s hs u hu a
    obtain ⟨hsmall, hbig⟩ := ha n hn
    have hre : (li ρ n).re = Fintype.card ι - ∑ i, (w i ^ n).re := by
      unfold li
      rw [re_sum]
      simp [sub_re, sum_sub_distrib, hw]
    have hsplit := sum_filter_add_sum_filter_not univ (fun i => ‖w i‖ = M) (fun i => (w i ^ n).re)
    have hA : M ^ n / 8 ≤ ∑ i ∈ s, (w i ^ n).re := by
      have e : ∀ i ∈ s, (w i ^ n).re = M ^ n * (u i ^ n).re := by
        intro i _
        have hwu : w i = (M : ℂ) * u i := by
          rw [hu_def]
          field_simp
        rw [hwu, mul_pow, ← ofReal_pow, re_ofReal_mul]
      rw [sum_congr rfl e, ← mul_sum]
      have hMn := pow_pos hM0 n
      nlinarith
    have hB : -(M ^ n / 16) ≤ ∑ i ∈ t, (w i ^ n).re := by
      have e : ∀ i ∈ t, -(M ^ n * q i ^ n) ≤ (w i ^ n).re := by
        intro i _
        have h1 := abs_re_le_norm (w i ^ n)
        have h2 : ‖w i ^ n‖ = M ^ n * q i ^ n := by
          rw [norm_pow, ← mul_pow, hq_def]
          congr 1
          field_simp
        have h3 := neg_abs_le (w i ^ n).re
        linarith
      have hMn := pow_pos hM0 n
      calc -(M ^ n / 16) ≤ -(M ^ n * ∑ i ∈ t, q i ^ n) := by nlinarith
        _ = ∑ i ∈ t, -(M ^ n * q i ^ n) := by rw [mul_sum, sum_neg_distrib]
        _ ≤ _ := sum_le_sum e
    have hp := hpos n
    rw [hre] at hp
    linarith

/-! ## 5. Li em cada mundo finito -/

/-- **Li no mundo finito `Z`**: se `ρ` enumera os zeros não triviais de altura `|Im| ≤ Z`, então RH até a altura
`Z` ⟺ todos os coeficientes de Li desses zeros são `≥ 0`. -/
theorem li_no_mundo {ι : Type*} [Fintype ι] (Zh : ℕ) (ρ : ι → ℂ)
    (hρ : Set.range ρ = {s | s ∈ Z ∧ |s.im| ≤ Zh}) :
    FiniteWorlds.RHateZ Zh ↔ ∀ n : ℕ, 0 ≤ (li ρ n).re := by
  have hmem : ∀ i, ρ i ∈ Z ∧ |(ρ i).im| ≤ Zh := by
    intro i
    have : ρ i ∈ Set.range ρ := ⟨i, rfl⟩
    rw [hρ] at this
    exact this
  have h0 : ∀ i, ρ i ≠ 0 := by
    intro i h
    have := (hmem i).1.2.1
    rw [h, zero_re] at this
    exact lt_irrefl 0 this
  have hsym : ∀ i, ∃ j, ρ j = 1 - ρ i := by
    intro i
    have h1 : 1 - ρ i ∈ Set.range ρ := by
      rw [hρ]
      refine ⟨tensao_mem_Z (hmem i).1, ?_⟩
      simp only [sub_im, one_im, zero_sub, abs_neg]
      exact (hmem i).2
    obtain ⟨j, hj⟩ := h1
    exact ⟨j, hj⟩
  rw [← li_finito ρ h0 hsym]
  constructor
  · intro h i
    obtain ⟨hz, hb⟩ := hmem i
    have hnt := ((mem_Z_iff_nao_trivial _).mp hz).2
    have hs1 : ρ i ≠ 1 := by
      intro h1
      have := hz.2.2
      rw [h1, one_re] at this
      exact lt_irrefl 1 this
    exact h (ρ i) hz.1 hnt hs1 hb
  · intro h s hz ht _ hb
    have hsZ : s ∈ Z := (mem_Z_iff_nao_trivial s).mpr ⟨hz, ht⟩
    have : s ∈ Set.range ρ := by rw [hρ]; exact ⟨hsZ, hb⟩
    obtain ⟨i, rfl⟩ := this
    exact h i

/-! ## 6. Teste de não vacuidade -/

/-- **O critério detecta a saída da reta**: a família `{¼, ¾}` (simétrica, zeros de `G` em
`Locks.simetria_nao_basta`) tem `λ₂ = −64/9 < 0`. -/
theorem li_detecta_fora_da_reta : (li ![(1 / 4 : ℂ), 3 / 4] 2).re = -64 / 9 := by
  have h : li ![(1 / 4 : ℂ), 3 / 4] 2 = -64 / 9 := by
    simp [li, cayley, Fin.sum_univ_two]
    norm_num
  rw [h]
  norm_num

end ClayRiemannProof.LiFinite
