import ClayRiemannProof.CertifiedZeros.Rectangle
import Mathlib.Analysis.Complex.AbsMax

/-!
# Certificado de `|ζ| ≤ U` num retângulo e o princípio do máximo num retângulo

O espelho de `Rectangle.lean` para cotas **superiores**:

* `nMaxSq`, `norm_le_de`: `‖z‖² ≤ max(lo², hi²)_Re + max(lo², hi²)_Im` para `z` num retângulo certificado `IC`;
* `chkS`, `chkS_spec`: o kernel confere `‖ζ(c)‖ ≤ u` em todos os centros de uma malha (com `zetaIG`);
* `certificado_malha_sup`, `certificado_derivada_sup`, **`peca_sup`**: se `‖ζ(c)‖ + (B/r)h ≤ U` em todos os
  centros, então `‖ζ‖ ≤ U` em todo o retângulo (`B = cotaQ` na região de Cauchy, como em `peca_ret`);
* **`maximo_ret`**: o princípio do máximo (`Complex.norm_le_of_forall_mem_frontier_norm_le`) num retângulo
  `[s0, s1] × [a, b]` com `a > 0`: uma cota de `‖ζ‖` nas quatro arestas vale no retângulo inteiro.

Com isso, uma cota de `|ζ|` medida só no **bordo de um quadrado** vira cota no quadrado cheio, que é o que a
fórmula de Cauchy pede (`LargerBall.lean`). Arquivo novo (não vem do ATK).
-/

open Complex Metric Set

namespace ClayRiemannProof.CertifiedZeros.UpperBound

open ClayRiemannProof.Cert.Interval ClayRiemannProof.CertifiedZeros.EulerMaclaurinData
  ClayRiemannProof.CertifiedZeros.CrudeBound ClayRiemannProof.CertifiedZeros.Evaluation
  ClayRiemannProof.CertifiedZeros.Rectangle

/-! ## 1. Cota superior da norma de um retângulo certificado -/

/-- `max(lo², hi²)`: cota superior de `x²` para `x ∈ [lo, hi]`. -/
def qMax (J : IR) : ℚ := max (J.lo ^ 2) (J.hi ^ 2)

/-- Cota superior de `‖z‖²` no retângulo `J`. -/
def nMaxSq (J : IC) : ℚ := qMax J.re + qMax J.im

theorem sq_le_qMax {x : ℝ} {J : IR} (h : IR.mem x J) : x ^ 2 ≤ (qMax J : ℝ) := by
  obtain ⟨h1, h2⟩ := h
  unfold qMax
  push_cast
  rcases le_total 0 x with hx | hx
  · exact (pow_le_pow_left₀ hx h2 2).trans (le_max_right _ _)
  · have : x ^ 2 ≤ (J.lo : ℝ) ^ 2 := by nlinarith
    exact this.trans (le_max_left _ _)

/-- **Cota superior certificada**: `0 ≤ u` e `nMaxSq J ≤ u²` ⟹ `‖z‖ ≤ u`. -/
theorem norm_le_de {z : ℂ} {J : IC} {u : ℚ} (h : IC.mem z J) (h0 : 0 ≤ u) (hu : nMaxSq J ≤ u ^ 2) :
    ‖z‖ ≤ (u : ℝ) := by
  have h1 : ‖z‖ ^ 2 ≤ ((u : ℚ) : ℝ) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have a := sq_le_qMax h.1
    have b := sq_le_qMax h.2
    have hu' : ((nMaxSq J : ℚ) : ℝ) ≤ ((u ^ 2 : ℚ) : ℝ) := by exact_mod_cast hu
    unfold nMaxSq at hu'
    push_cast at hu'
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg z) (by exact_mod_cast h0) (by norm_num)).mp h1

/-! ## 2. A verificação dos centros -/

/-- Verificação de `‖ζ(c)‖ ≤ u` em todos os centros, pelo kernel. -/
def chkS (N M K nT p : ℕ) (s0 hs a ht u : ℚ) (ns nt : ℕ) : Bool :=
  (List.range ns).all fun i : ℕ => (List.range nt).all fun j : ℕ =>
    okAllG N K nT p (s0 + hs * (2 * (i : ℚ) + 1)) (a + ht * (2 * (j : ℚ) + 1)) &&
      decide (nMaxSq (zetaIG N M K nT p (s0 + hs * (2 * (i : ℚ) + 1)) (a + ht * (2 * (j : ℚ) + 1))) ≤ u ^ 2)

theorem chkS_spec {N M K nT p : ℕ} {s0 hs a ht u : ℚ} {ns nt : ℕ} (hN : 1 ≤ N) (hM1 : 1 ≤ M)
    (hM : M ≤ 10) (hs0 : 0 < s0) (hhs : 0 ≤ hs) (ha : 0 < a) (hht : 0 ≤ ht) (hu : 0 ≤ u)
    (hc : chkS N M K nT p s0 hs a ht u ns nt = true) :
    ∀ c ∈ centrosR s0 hs a ht ns nt, ‖riemannZeta c‖ ≤ (u : ℝ) := by
  intro c hcen
  obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hcen
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
  unfold chkS at hc
  rw [List.all_eq_true] at hc
  have h1 := hc i (List.mem_range.mpr (Finset.mem_range.mp hi))
  rw [List.all_eq_true] at h1
  have h2 := h1 j (List.mem_range.mpr (Finset.mem_range.mp hj))
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  obtain ⟨hok, hle⟩ := h2
  have hσ : 0 < s0 + hs * (2 * (i : ℚ) + 1) := by positivity
  have ht : a + ht * (2 * (j : ℚ) + 1) ≠ 0 := by positivity
  exact norm_le_de (mem_zetaIG hN hM1 hM hσ _ ht hok) hu hle

/-! ## 3. Malha e derivada: cota superior -/

/-- **Certificado de malha superior**: centros a distância `≤ h`, variação `≤ L·h` e `‖f(c)‖ + L·h ≤ U`
⟹ `‖f‖ ≤ U`. -/
theorem certificado_malha_sup {f : ℂ → ℂ} {K' : Set ℂ} {C : Finset ℂ} {h L U : ℝ}
    (hcov : ∀ z ∈ K', ∃ c ∈ C, ‖z - c‖ ≤ h)
    (hvar : ∀ z ∈ K', ∀ c ∈ C, ‖z - c‖ ≤ h → ‖f z - f c‖ ≤ L * h)
    (hval : ∀ c ∈ C, ‖f c‖ + L * h ≤ U) : ∀ z ∈ K', ‖f z‖ ≤ U := by
  intro z hz
  obtain ⟨c, hc, hzc⟩ := hcov z hz
  have h1 := hvar z hz c hc hzc
  have h2 := hval c hc
  have h3 : ‖f z‖ ≤ ‖f c‖ + ‖f z - f c‖ := norm_le_insert' _ _
  linarith

theorem certificado_derivada_sup {f : ℂ → ℂ} {V K' : Set ℂ} {C : Finset ℂ} {h L U : ℝ}
    (hV : Convex ℝ V) (hKV : K' ⊆ V) (hCV : ∀ c ∈ C, c ∈ V)
    (hd : ∀ x ∈ V, DifferentiableAt ℂ f x) (hb : ∀ x ∈ V, ‖deriv f x‖ ≤ L) (hL : 0 ≤ L)
    (hcov : ∀ z ∈ K', ∃ c ∈ C, ‖z - c‖ ≤ h) (hval : ∀ c ∈ C, ‖f c‖ + L * h ≤ U) :
    ∀ z ∈ K', ‖f z‖ ≤ U := by
  refine certificado_malha_sup hcov (fun z hz c hc hzc => ?_) hval
  have := hV.norm_image_sub_le_of_norm_deriv_le hd hb (hCV c hc) (hKV hz)
  calc ‖f z - f c‖ ≤ L * ‖z - c‖ := this
    _ ≤ L * h := mul_le_mul_of_nonneg_left hzc hL

/-- **Uma peça retangular com cota superior, a partir de dados racionais.** -/
theorem peca_sup {s0 s1 a b r B hs ht h u U R d : ℚ} {ns nt Nc Mc Ne Me K nT p : ℕ}
    (hr : 0 < r) (hrs : r < s0) (hra : r < a) (hns : 1 ≤ ns) (hnt : 1 ≤ nt) (hhs : 0 < hs)
    (hht : 0 < ht) (hs1 : s0 + 2 * hs * ns = s1) (hb : a + 2 * ht * nt = b) (hh0 : 0 ≤ h)
    (hh : hs ^ 2 + ht ^ 2 ≤ h ^ 2)
    (hR : (s1 + r) ^ 2 + (b + r) ^ 2 ≤ R ^ 2) (hR0 : 0 ≤ R) (hd0 : 0 < d) (hd : d ≤ a - r)
    (hNc : 1 ≤ Nc) (hMc : 2 ≤ Mc) (hMc10 : Mc ≤ 10) (hBq : cotaQ Nc Mc R d ≤ B) (hB0 : 0 ≤ B)
    (hU : u + B / r * h ≤ U) (hu0 : 0 ≤ u)
    (hNe : 1 ≤ Ne) (hMe : 1 ≤ Me) (hMe10 : Me ≤ 10)
    (hchk : chkS Ne Me K nT p s0 hs a ht u ns nt = true) :
    ∀ z ∈ ret s0 s1 a b, ‖riemannZeta z‖ ≤ (U : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have castle : ∀ {x y : ℚ}, x ≤ y → (x : ℝ) ≤ y := fun h => by exact_mod_cast h
  have hB : ∀ w : ℂ, (s0 : ℝ) - r ≤ w.re → w.re ≤ (s1 : ℝ) + r → (a : ℝ) - r ≤ w.im →
      w.im ≤ (b : ℝ) + r → ‖riemannZeta w‖ ≤ (B : ℝ) := by
    intro w h1 h2 h3 h4
    have hR' : ((s1 : ℝ) + r) ^ 2 + ((b : ℝ) + r) ^ 2 ≤ (R : ℝ) ^ 2 := by
      have := castle hR
      push_cast at this
      exact this
    have hd' : (d : ℝ) ≤ (a : ℝ) - r := by
      have := castle hd
      push_cast at this
      exact this
    obtain ⟨p0, p1, p2, p3⟩ := reg_ret (by exact_mod_cast hrs) (by exact_mod_cast hra) hR'
      (by exact_mod_cast hR0) (by exact_mod_cast hd0) hd' h1 h2 h3 h4
    have hc := cota_geral hNc hMc p0 p1 p2 (by exact_mod_cast hd0) p3
    rw [← cotaQ_spec hMc10] at hc
    exact hc.trans (castle hBq)
  have hs1' : ((s0 : ℚ) : ℝ) + 2 * ((hs : ℚ) : ℝ) * ns = ((s1 : ℚ) : ℝ) := by
    rw [← hs1]; push_cast; ring
  have hb' : ((a : ℚ) : ℝ) + 2 * ((ht : ℚ) : ℝ) * nt = ((b : ℚ) : ℝ) := by
    rw [← hb]; push_cast; ring
  have hs0 : 0 < s0 := lt_trans hr hrs
  have ha : 0 < a := lt_trans hr hra
  have hval : ∀ c ∈ centrosR s0 hs a ht ns nt, ‖riemannZeta c‖ + (B : ℝ) / r * h ≤ U := by
    intro c hc
    have h1 := chkS_spec hNe hMe hMe10 hs0 hhs.le ha hht.le hu0 hchk c hc
    have h2 : ((u : ℚ) : ℝ) + (B : ℝ) / r * h ≤ U := by
      have := castle hU
      push_cast at this
      exact this
    linarith
  refine certificado_derivada_sup (convex_ret s0 s1 a b) subset_rfl
    (centrosR_ret hhs.le hht.le hs1'.le hb'.le) (fun x hx => ?_)
    (fun x hx => deriv_cota_ret hr' (by exact_mod_cast hra) hB hx) (div_nonneg (by exact_mod_cast hB0) hr'.le)
    (cobre_ret hns hnt hhs hht hh0 hh hs1'.ge hb'.ge) hval
  apply differentiableAt_riemannZeta
  intro e
  have := hx.2.2.1
  rw [e, one_im] at this
  have : (0 : ℝ) < a := by exact_mod_cast ha
  linarith

/-! ## 4. O princípio do máximo num retângulo -/

theorem ret_eq_reProdIm (s0 s1 a b : ℝ) : ret s0 s1 a b = Icc s0 s1 ×ℂ Icc a b := by
  ext z
  simp only [ret, mem_ofPred_eq, Complex.mem_reProdIm, mem_Icc]
  tauto

/-- **Princípio do máximo no retângulo**: se `‖ζ‖ ≤ U` nas quatro arestas de `[s0, s1] × [a, b]` (`a > 0`),
então `‖ζ‖ ≤ U` no retângulo inteiro. -/
theorem maximo_ret {s0 s1 a b U : ℝ} (hs : s0 ≤ s1) (hab : a ≤ b) (ha : 0 < a)
    (hU : ∀ z ∈ ret s0 s1 a b, (z.re = s0 ∨ z.re = s1 ∨ z.im = a ∨ z.im = b) → ‖riemannZeta z‖ ≤ U) :
    ∀ z ∈ ret s0 s1 a b, ‖riemannZeta z‖ ≤ U := by
  intro z hz
  rw [ret_eq_reProdIm] at hz hU
  have hcl : closure (Icc s0 s1 ×ℂ Icc a b) = Icc s0 s1 ×ℂ Icc a b := by
    rw [Complex.closure_reProdIm, closure_Icc, closure_Icc]
  refine Complex.norm_le_of_forall_mem_frontier_norm_le
    ((Metric.isBounded_Icc s0 s1).reProdIm (Metric.isBounded_Icc a b)) ?_ ?_ (subset_closure hz)
  · apply DifferentiableOn.diffContOnCl
    rw [hcl]
    refine Rectangle.difOn_zeta.mono fun w hw => ?_
    simp only [mem_compl_iff, mem_singleton_iff]
    intro e
    have := (Complex.mem_reProdIm.mp hw).2.1
    rw [e, one_im] at this
    linarith
  · intro w hw
    rw [Complex.frontier_reProdIm, closure_Icc, closure_Icc, frontier_Icc hs, frontier_Icc hab] at hw
    rcases hw with hw | hw
    · obtain ⟨h1, h2⟩ := Complex.mem_reProdIm.mp hw
      have hw' : w ∈ Icc s0 s1 ×ℂ Icc a b := by
        refine Complex.mem_reProdIm.mpr ⟨h1, ?_⟩
        rcases h2 with h2 | h2
        · rw [h2]; exact ⟨le_rfl, hab⟩
        · rw [mem_singleton_iff.mp h2]; exact ⟨hab, le_rfl⟩
      refine hU w hw' ?_
      rcases h2 with h2 | h2
      · exact Or.inr (Or.inr (Or.inl h2))
      · exact Or.inr (Or.inr (Or.inr (mem_singleton_iff.mp h2)))
    · obtain ⟨h1, h2⟩ := Complex.mem_reProdIm.mp hw
      have hw' : w ∈ Icc s0 s1 ×ℂ Icc a b := by
        refine Complex.mem_reProdIm.mpr ⟨?_, h2⟩
        rcases h1 with h1 | h1
        · rw [h1]; exact ⟨le_rfl, hs⟩
        · rw [mem_singleton_iff.mp h1]; exact ⟨hs, le_rfl⟩
      refine hU w hw' ?_
      rcases h1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl (mem_singleton_iff.mp h1))

end ClayRiemannProof.CertifiedZeros.UpperBound
