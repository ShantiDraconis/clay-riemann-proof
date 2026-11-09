import ClayRiemannProof.Toeplitz
import ClayRiemannProof.WeilXi
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A rota pelas grades: (A) sem hipótese contínua, e a simplicidade pela queda estrita (§65)

Uma forma quadrática invariante por translação (como a de Weil, que só depende de `g ⋆ g̃`), restrita às funções-degrau
numa grade uniforme de passo `δ`, tem matriz de Toeplitz na base das células. Este arquivo fecha no kernel a versão
discreta do passo (A) de Connes–van Suijlekom, sem teoria espectral contínua:

1. `simples_de_queda`: se a forma da matriz `M` (por exemplo `M = T − μ·1`, `μ` o menor autovalor) não se anula em
   vetor nenhum da seção sem a última linha e coluna, então o núcleo de `M` é a reta de qualquer `ξ ≠ 0` nele. Isto é a
   simplicidade (S) na grade, dada pela **queda estrita** do menor autovalor quando a grade ganha uma célula.
2. `integral_celula`, `transfDegrau_eq`: a transformada de Fourier da função-degrau `Σ ξ_j 1_{[jδ, (j+1)δ]}` é
   `ĝ(r) = δ·φ(irδ)·P(e^{irδ})`, com `φ = dslope exp 0` inteira (`φ(z) = (e^z − 1)/z`).
3. `zeros_reais_degrau`: se `P` só tem zeros no círculo unitário, `ĝ` só tem zeros reais.
4. `degrau_minimizante_zeros_reais`: juntando com `Toeplitz.zeros_no_circulo`, **o minimizante de uma forma de Toeplitz
   em funções-degrau tem transformada só com zeros reais, sempre que houver queda estrita.**
5. `hurwitz_reais`: o limite localmente uniforme de funções inteiras só com zeros reais só tem zeros reais (onde não é
   identicamente nulo).
6. `rh_de_grades`: se uma sequência de minimizantes em grades (com queda estrita em cada uma) tem transformadas que
   convergem localmente uniformemente para `Ξ`, a RH vale.

7. `sem_queda_nao_simples`, `simples_iff_queda`: a recíproca de 1. Para matrizes de Toeplitz semidefinidas
   positivas, **(S) na grade ⟺ queda estrita**: sem queda, o minimizante da seção aparece duas vezes, em `[x; 0]` e em
   `[0; x]`.

O que sobra como hipótese em `rh_de_grades` é só a convergência. A queda estrita é uma desigualdade finita em cada grade.
Nada aqui prova RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Grade

open Finset Matrix Complex Filter Topology ClayRiemannProof.Toeplitz ClayRiemannProof.WeilXi

open scoped ComplexOrder

/-! ## 1. A simplicidade pela queda estrita -/

/-- **A forma de um vetor com a última coordenada nula é a forma da seção.** -/
theorem forma_secao {N : ℕ} (M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) (u : Fin (N + 1) → ℂ)
    (hu : u (Fin.last N) = 0) :
    star u ⬝ᵥ M *ᵥ u = star (u ∘ Fin.castSucc) ⬝ᵥ (M.submatrix Fin.castSucc Fin.castSucc) *ᵥ (u ∘ Fin.castSucc) := by
  simp only [dotProduct, mulVec, Pi.star_apply, Function.comp_apply, submatrix_apply]
  rw [Fin.sum_univ_castSucc]
  simp only [hu, star_zero, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_castSucc, hu, mul_zero, add_zero]

/-- **A queda estrita dá a simplicidade.** Se a forma de `M` restrita à seção (sem a última linha e coluna) só se anula
no zero, então o núcleo de `M` é a reta de qualquer `ξ ≠ 0` nele. -/
theorem simples_de_queda {N : ℕ} {M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ}
    (hsec : ∀ x : Fin N → ℂ, star x ⬝ᵥ (M.submatrix Fin.castSucc Fin.castSucc) *ᵥ x = 0 → x = 0)
    {ξ : Fin (N + 1) → ℂ} (hξ : M *ᵥ ξ = 0) (hξ0 : ξ ≠ 0) :
    ∀ v : Fin (N + 1) → ℂ, M *ᵥ v = 0 → ∃ c : ℂ, v = c • ξ := by
  -- um vetor do núcleo com a última coordenada nula é zero
  have chave : ∀ u : Fin (N + 1) → ℂ, M *ᵥ u = 0 → u (Fin.last N) = 0 → u = 0 := by
    intro u hu hl
    have h0 : star (u ∘ Fin.castSucc) ⬝ᵥ (M.submatrix Fin.castSucc Fin.castSucc) *ᵥ (u ∘ Fin.castSucc) = 0 := by
      rw [← forma_secao M u hl, hu, dotProduct_zero]
    have h1 := hsec _ h0
    funext i
    induction i using Fin.lastCases with
    | last => exact hl
    | cast j => exact congrFun h1 j
  have hl : ξ (Fin.last N) ≠ 0 := fun h => hξ0 (chave ξ hξ h)
  intro v hv
  refine ⟨v (Fin.last N) / ξ (Fin.last N), ?_⟩
  have hu : M *ᵥ (v - (v (Fin.last N) / ξ (Fin.last N)) • ξ) = 0 := by
    rw [mulVec_sub, mulVec_smul, hv, hξ, smul_zero, sub_zero]
  have h2 := chave _ hu (by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring)
  exact sub_eq_zero.mp h2

/-! ## 2. A transformada da função-degrau -/

/-- `φ(z) = (e^z − 1)/z`, inteira (`φ(0) = 1`). -/
noncomputable def fi : ℂ → ℂ := dslope cexp 0

theorem differentiable_fi : Differentiable ℂ fi := by
  intro z
  have h : DifferentiableOn ℂ (dslope cexp 0) Set.univ :=
    (Complex.differentiableOn_dslope Filter.univ_mem).mpr differentiable_exp.differentiableOn
  exact (h z (Set.mem_univ z)).differentiableAt Filter.univ_mem

theorem fi_zero : fi 0 = 1 := by
  simp [fi, dslope_same, Complex.deriv_exp]

theorem fi_of_ne {z : ℂ} (hz : z ≠ 0) : fi z = (cexp z - 1) / z := by
  simp [fi, dslope_of_ne _ hz, slope_def_field]

/-- Se `φ(z) = 0` então `e^z = 1`. -/
theorem exp_de_fi_zero {z : ℂ} (h : fi z = 0) : cexp z = 1 := by
  by_cases hz : z = 0
  · rw [hz, fi_zero] at h
    exact absurd h one_ne_zero
  · rw [fi_of_ne hz, div_eq_zero_iff] at h
    rcases h with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hz

/-- **A integral numa célula**: `∫_{jδ}^{(j+1)δ} e^{irx} dx = δ·(e^{irδ})^j·φ(irδ)`. -/
theorem integral_celula (δ : ℝ) (r : ℂ) (j : ℕ) :
    ∫ x in ((j : ℝ) * δ)..(((j : ℝ) + 1) * δ), cexp (I * r * x) = δ * cexp (I * r * δ) ^ j * fi (I * r * δ) := by
  by_cases hc : I * r * δ = 0
  · have hc' : I * r = 0 ∨ (δ : ℂ) = 0 := mul_eq_zero.mp hc
    rcases hc' with h | h
    · simp only [h, zero_mul, Complex.exp_zero, intervalIntegral.integral_const, mul_one, one_pow, fi_zero]
      rw [Complex.real_smul]
      push_cast
      ring
    · have hδ : δ = 0 := by exact_mod_cast h
      subst hδ
      simp
  · have hIr : I * r ≠ 0 := by
      intro h
      apply hc
      rw [h, zero_mul]
    rw [integral_exp_mul_complex hIr, fi_of_ne hc, ← Complex.exp_nat_mul]
    have hδ : (δ : ℂ) ≠ 0 := by
      intro h
      apply hc
      rw [h, mul_zero]
    push_cast
    field_simp
    rw [show I * r * ((j : ℂ) + 1) * (δ : ℂ) = I * r * j * δ + I * r * δ by ring, Complex.exp_add]
    ring

/-- A transformada de Fourier da função-degrau `Σ_j ξ_j 1_{[jδ, (j+1)δ]}`, célula por célula. -/
noncomputable def transfDegrau {n : ℕ} (δ : ℝ) (ξ : Fin n → ℂ) (r : ℂ) : ℂ :=
  ∑ j : Fin n, ξ j * ∫ x in ((j : ℝ) * δ)..(((j : ℝ) + 1) * δ), cexp (I * r * x)

/-- O polinômio do vetor `ξ`. -/
noncomputable def polin {n : ℕ} (ξ : Fin n → ℂ) (w : ℂ) : ℂ := ∑ j : Fin n, ξ j * w ^ (j : ℕ)

/-- **`ĝ(r) = δ·φ(irδ)·P(e^{irδ})`.** -/
theorem transfDegrau_eq {n : ℕ} (δ : ℝ) (ξ : Fin n → ℂ) (r : ℂ) :
    transfDegrau δ ξ r = δ * fi (I * r * δ) * polin ξ (cexp (I * r * δ)) := by
  unfold transfDegrau polin
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_celula]
  ring

theorem differentiable_transfDegrau {n : ℕ} (δ : ℝ) (ξ : Fin n → ℂ) : Differentiable ℂ (transfDegrau δ ξ) := by
  have h : transfDegrau δ ξ = fun r => δ * fi (I * r * δ) * polin ξ (cexp (I * r * δ)) :=
    funext (transfDegrau_eq δ ξ)
  rw [h]
  unfold polin
  have hfi : Differentiable ℂ fun r : ℂ => fi (I * r * δ) := differentiable_fi.comp (by fun_prop)
  fun_prop

/-- `|e^{irδ}| = 1` com `δ > 0` força `r` real. -/
theorem im_de_norma_exp {δ : ℝ} (hδ : 0 < δ) {r : ℂ} (h : ‖cexp (I * r * δ)‖ = 1) : r.im = 0 := by
  rw [Complex.norm_exp] at h
  have hre : (I * r * δ).re = -(r.im * δ) := by simp
  rw [hre, Real.exp_eq_one_iff, neg_eq_zero] at h
  rcases mul_eq_zero.mp h with h' | h'
  · exact h'
  · exact absurd h' hδ.ne'

/-- **Zeros no círculo dão zeros reais**: se `P` só tem zeros com `|w| = 1`, então `ĝ` só tem zeros reais. -/
theorem zeros_reais_degrau {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {ξ : Fin n → ℂ}
    (hP : ∀ w : ℂ, polin ξ w = 0 → ‖w‖ = 1) {r : ℂ} (hr : transfDegrau δ ξ r = 0) : r.im = 0 := by
  rw [transfDegrau_eq] at hr
  apply im_de_norma_exp hδ
  rcases mul_eq_zero.mp hr with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd (by exact_mod_cast h' : δ = 0) hδ.ne'
    · rw [exp_de_fi_zero h', norm_one]
  · exact hP _ h

/-- **Qualquer base de translados**: se `ĝ(r) = Φ(r)·P(e^{irδ})`, com `Φ` só com zeros reais (a transformada do
gerador) e `P` só com zeros no círculo, então `ĝ` só tem zeros reais. Vale para os B-splines de ordem `p`, cuja
transformada é `(δ·φ(irδ))^p` vezes uma fase (`zeros_reais_bspline`). -/
theorem zeros_reais_translados {Φ : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ) (hΦ : ∀ r, Φ r = 0 → r.im = 0) {n : ℕ}
    {ξ : Fin n → ℂ} (hP : ∀ w : ℂ, polin ξ w = 0 → ‖w‖ = 1) {r : ℂ}
    (hr : Φ r * polin ξ (cexp (I * r * δ)) = 0) : r.im = 0 := by
  rcases mul_eq_zero.mp hr with h | h
  · exact hΦ r h
  · exact im_de_norma_exp hδ (hP _ h)

/-- A transformada do B-spline de ordem `p`, `(δ·φ(irδ))^p` (a menos de fase), só tem zeros reais. -/
theorem zeros_reais_bspline {δ : ℝ} (hδ : 0 < δ) (p : ℕ) {r : ℂ} (h : ((δ : ℂ) * fi (I * r * δ)) ^ p = 0) :
    r.im = 0 := by
  rcases mul_eq_zero.mp (pow_eq_zero_iff'.mp h).1 with h' | h'
  · exact absurd (by exact_mod_cast h' : δ = 0) hδ.ne'
  · apply im_de_norma_exp hδ
    rw [exp_de_fi_zero h', norm_one]

/-! ## 3. O minimizante numa grade -/

/-- **O minimizante numa grade tem transformada só com zeros reais.** Seja `M` de Toeplitz (`M i j = t(i − j)`),
semidefinida positiva (por exemplo `T − μ·G` com `μ` o menor autovalor generalizado), com `M ξ = 0`, `ξ ≠ 0`, e com
queda estrita (a forma de `M` na seção só se anula no zero). Então a transformada da função-degrau de `ξ` só tem zeros
reais, em qualquer passo `δ > 0`. -/
theorem degrau_minimizante_zeros_reais {N : ℕ} {M : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ} {t : ℤ → ℂ}
    (hToe : ∀ i j : Fin (N + 1), M i j = t ((i : ℤ) - j)) (hM : M.PosSemidef)
    (hsec : ∀ x : Fin N → ℂ, star x ⬝ᵥ (M.submatrix Fin.castSucc Fin.castSucc) *ᵥ x = 0 → x = 0)
    {ξ : Fin (N + 1) → ℂ} (hξ : M *ᵥ ξ = 0) (hξ0 : ξ ≠ 0) {δ : ℝ} (hδ : 0 < δ) :
    ∀ r : ℂ, transfDegrau δ ξ r = 0 → r.im = 0 := by
  intro r hr
  refine zeros_reais_degrau hδ (fun w hw => ?_) hr
  exact zeros_no_circulo hToe hM hξ hξ0 (simples_de_queda hsec hξ hξ0) hw

/-! ## 4. Hurwitz na reta real e a rota completa -/

/-- **Hurwitz na reta real**: se funções inteiras só com zeros reais convergem localmente uniformemente para `g`, todo
zero de `g` onde `g` não é identicamente nula é real. -/
theorem hurwitz_reais {G : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hG : ∀ n, Differentiable ℂ (G n))
    (hA : ∀ n r, G n r = 0 → r.im = 0) (hconv : TendstoLocallyUniformly G g atTop) {z : ℂ} (hz : g z = 0)
    (hnz : ¬ ∀ᶠ w in 𝓝 z, g w = 0) : z.im = 0 := by
  have hconv' : TendstoLocallyUniformlyOn G g atTop Set.univ := tendstoLocallyUniformlyOn_univ.mpr hconv
  have hgd : DifferentiableOn ℂ g Set.univ :=
    hconv'.differentiableOn (Eventually.of_forall fun n => (hG n).differentiableOn) isOpen_univ
  have hiso : ∀ᶠ w in 𝓝[≠] z, g w ≠ 0 :=
    ((hgd.analyticAt Filter.univ_mem).eventually_eq_zero_or_eventually_ne_zero).resolve_left hnz
  rw [eventually_nhdsWithin_iff] at hiso
  obtain ⟨r₀, hr₀, hball⟩ := Metric.eventually_nhds_iff.mp hiso
  have chave : ∀ r : ℝ, 0 < r → r < r₀ → |z.im| ≤ r := by
    intro r hr hrr
    have hev := WeilRota.hurwitz_passo hr (fun n => (hG n).differentiableOn)
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hconv' _ (Set.subset_univ _)
        (isCompact_closedBall z r))
      (hgd.continuousOn.mono (Set.subset_univ _)) hz
      (fun w hw => by
        have hd : dist w z = r := Metric.mem_sphere.mp hw
        refine hball (by rw [hd]; exact hrr) ?_
        intro h
        rw [h, dist_self] at hd
        exact hr.ne hd)
    obtain ⟨n, w, hw, hw0⟩ := hev.exists
    have hwim := hA n w hw0
    have hdist : dist w z ≤ r := Metric.mem_closedBall.mp hw
    rw [dist_eq_norm] at hdist
    have := Complex.abs_im_le_norm (w - z)
    rw [Complex.sub_im, hwim, zero_sub, abs_neg] at this
    linarith
  by_contra hne
  have hd : 0 < |z.im| := abs_pos.mpr hne
  have h := chave (min (|z.im| / 2) (r₀ / 2)) (by positivity) (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have := min_le_left (|z.im| / 2) (r₀ / 2)
  linarith

/-- **A rota pelas grades.** Para cada `k`, um minimizante `ξ k` numa grade de passo `δ k > 0` e `N k + 1` células,
com matriz de Toeplitz semidefinida positiva e queda estrita. Se as transformadas das funções-degrau convergem
localmente uniformemente para `Ξ`, a RH vale. -/
theorem rh_de_grades {N : ℕ → ℕ} {M : (k : ℕ) → Matrix (Fin (N k + 1)) (Fin (N k + 1)) ℂ} {t : ℕ → ℤ → ℂ}
    (hToe : ∀ k, ∀ i j : Fin (N k + 1), M k i j = t k ((i : ℤ) - j)) (hM : ∀ k, (M k).PosSemidef)
    (hsec : ∀ k, ∀ x : Fin (N k) → ℂ,
      star x ⬝ᵥ ((M k).submatrix Fin.castSucc Fin.castSucc) *ᵥ x = 0 → x = 0)
    {ξ : (k : ℕ) → Fin (N k + 1) → ℂ} (hξ : ∀ k, M k *ᵥ ξ k = 0) (hξ0 : ∀ k, ξ k ≠ 0)
    {δ : ℕ → ℝ} (hδ : ∀ k, 0 < δ k)
    (hconv : TendstoLocallyUniformly (fun k => transfDegrau (δ k) (ξ k)) Xi atTop) : RiemannHypothesis := by
  rw [rh_iff_Xi_zeros_reais]
  intro r hr
  exact hurwitz_reais (fun k => differentiable_transfDegrau (δ k) (ξ k))
    (fun k => degrau_minimizante_zeros_reais (hToe k) (hM k) (hsec k) (hξ k) (hξ0 k) (hδ k)) hconv hr
    (inteira_nao_some differentiable_Xi ⟨WeilRota.altura 0, by rw [Xi_altura, ClayRiemannProof.Xi.xi_zero]; norm_num⟩ r)

/-! ## 5. A recíproca: sem queda estrita, o menor autovalor não é simples -/

/-- Acrescentar uma coordenada nula não muda a forma de Toeplitz. -/
theorem forma_succ {m : ℕ} (t : ℤ → ℂ) {u w : ℕ → ℂ} (hu : u m = 0) (hw : w m = 0) :
    forma (m + 1) t u w = forma m t u w := by
  unfold forma
  rw [Finset.sum_range_succ]
  simp only [hu, star_zero, zero_mul, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_range_succ, hw, mul_zero, add_zero]

/-- **Sem queda estrita, o núcleo tem dimensão ≥ 2.** Se a forma de `M` (de Toeplitz, semidefinida positiva) se anula
num `x ≠ 0` da seção, então `[x; 0]` e `[0; x]` estão no núcleo de `M` e não são proporcionais: pela invariância de
translação, o minimizante da seção aparece duas vezes. -/
theorem sem_queda_nao_simples {N : ℕ} {M : Matrix (Fin (N + 2)) (Fin (N + 2)) ℂ} {t : ℤ → ℂ}
    (hToe : ∀ i j : Fin (N + 2), M i j = t ((i : ℤ) - j)) (hM : M.PosSemidef) {x : Fin (N + 1) → ℂ}
    (hx0 : x ≠ 0) (hx : star x ⬝ᵥ (M.submatrix Fin.castSucc Fin.castSucc) *ᵥ x = 0) :
    ∃ u v : Fin (N + 2) → ℂ, M *ᵥ u = 0 ∧ M *ᵥ v = 0 ∧ u ≠ 0 ∧ ∀ c : ℂ, v ≠ c • u := by
  set X : ℕ → ℂ := ext x with hXdef
  have hX : ∀ j, N + 1 ≤ j → X j = 0 := fun j hj => by
    have hj' : ¬ j < N + 1 := by omega
    simp [hXdef, Toeplitz.ext, hj']
  have hSX : ∀ j, N + 2 ≤ j → Sh X j = 0 := by
    intro j hj
    cases j with
    | zero => omega
    | succ i => exact hX i (by omega)
  have eU : ext (toFin (n := N + 2) X) = X := ext_toFin fun j hj => hX j (by omega)
  have eV : ext (toFin (n := N + 2) (Sh X)) = Sh X := ext_toFin hSX
  have hToe' : ∀ i j : Fin (N + 1), M.submatrix Fin.castSucc Fin.castSucc i j = t ((i : ℤ) - j) := by
    intro i j
    simp [submatrix_apply, hToe]
  have h0 : forma (N + 1) t X X = 0 := by
    rw [← forma_eq hToe' x x]
    exact hx
  have hU : star (toFin (n := N + 2) X) ⬝ᵥ M *ᵥ toFin (n := N + 2) X = 0 := by
    rw [forma_eq hToe, eU, forma_succ t (hX _ le_rfl) (hX _ le_rfl), h0]
  have hV : star (toFin (n := N + 2) (Sh X)) ⬝ᵥ M *ᵥ toFin (n := N + 2) (Sh X) = 0 := by
    rw [forma_eq hToe, eV, forma_desloca t hX hX, forma_succ t (hX _ le_rfl) (hX _ le_rfl), h0]
  refine ⟨toFin X, toFin (Sh X), hM.dotProduct_mulVec_zero_iff.mp hU, hM.dotProduct_mulVec_zero_iff.mp hV, ?_, ?_⟩
  · intro h
    apply hx0
    funext i
    have := congrFun h i.castSucc
    simp only [toFin, Fin.val_castSucc, Pi.zero_apply] at this
    rw [← ext_val x i, ← hXdef]
    exact this
  · intro c hc
    have hrel : ∀ j, j < N + 1 + 1 → Sh X j = c * X j := by
      intro j hj
      have := congrFun hc ⟨j, hj⟩
      simpa [toFin] using this
    have hX0 := desloca_autovetor hX c hrel
    apply hx0
    funext i
    rw [← ext_val x i, ← hXdef, hX0]
    rfl

/-- **Na grade, (S) ⟺ queda estrita.** Para `M` de Toeplitz, semidefinida positiva, com `ξ ≠ 0` no núcleo: o núcleo é
a reta de `ξ` (o menor autovalor é simples) exatamente quando a forma não se anula em vetor nenhum da seção. -/
theorem simples_iff_queda {N : ℕ} {M : Matrix (Fin (N + 2)) (Fin (N + 2)) ℂ} {t : ℤ → ℂ}
    (hToe : ∀ i j : Fin (N + 2), M i j = t ((i : ℤ) - j)) (hM : M.PosSemidef)
    {ξ : Fin (N + 2) → ℂ} (hξ : M *ᵥ ξ = 0) (hξ0 : ξ ≠ 0) :
    (∀ v : Fin (N + 2) → ℂ, M *ᵥ v = 0 → ∃ c : ℂ, v = c • ξ) ↔
      (∀ x : Fin (N + 1) → ℂ, star x ⬝ᵥ (M.submatrix Fin.castSucc Fin.castSucc) *ᵥ x = 0 → x = 0) := by
  constructor
  · intro hsimp x hx
    by_contra hx0
    obtain ⟨u, v, hu, hv, hu0, hind⟩ := sem_queda_nao_simples hToe hM hx0 hx
    obtain ⟨a, ha⟩ := hsimp u hu
    obtain ⟨b, hb⟩ := hsimp v hv
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hu0 (by rw [ha, zero_smul])
    apply hind (b / a)
    rw [hb, ha, smul_smul, div_mul_cancel₀ b ha0]
  · intro hsec
    exact simples_de_queda hsec hξ hξ0

end ClayRiemannProof.Grade
