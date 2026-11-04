import ClayRiemannProof.Maquina

/-!
# Os nós onde as pontes se encontram, e as lacunas L5 e L6 fechadas no modelo

As pontes do repositório (§36–§43) passam por poucos nós. Cada nó é **um** enunciado, e cada família de zeta só
muda o nome das letras:

1. **O nó do discriminante** (`no_discriminante`). Para `q > 1` e `λ` real, são equivalentes:
   (1) `λ² ≤ 4q`;
   (2) positividade: `m² − λmn + qn² ≥ 0` para todos `m, n` (Hodge/Castelnuovo, Weil);
   (3) círculo: as raízes de `1 − λu + qu²` têm `|u|² = 1/q` (zeta de Ihara, zeta de uma curva);
   (4) Frobenius: as raízes de `α² − λα + q` têm `|α|² = q` (Weil: autovalores de módulo `√q`);
   (5) reta: os zeros de `1 − λq^{−s} + q·q^{−2s}` têm `Re s = ½`.
   Hasse (curvas), Ramanujan (grafos), a positividade de Weil e a reta crítica são o **mesmo nó**.
   (`frobenius_iff_circulo`, `reta_iff_circulo`, `todo_u_eh_potencia`.)
2. **O nó simetria = conjugação** (`equacao_funcional_local`, `simetria_eh_conjugacao`). A equação funcional leva
   `u` em `1/(qu)` (como `s ↦ 1 − s`); a conjugação leva `u` em `ū` (como `s ↦ s̄`). Estar no círculo é exatamente o
   parceiro da equação funcional ser o conjugado: `|u|² = 1/q ⟺ ū = 1/(qu)`. Para ζ é
   `Zeta.Symmetry.torcao_fixo_iff` (`1 − ρ̄ = ρ ⟺ Re ρ = ½`). A RH, em todas as famílias, é "os dois parceiros
   coincidem".
3. **O nó espectral** (autoadjunto ⟹ autovalor real ⟹ reta): `Biblioteca.rh_de_hilbertPolya`,
   `Geometrias.selberg_reta`, `Geometrias.Ramanujan`. **O nó Π₁** (refutação finita): `Maquina.refutacao_finita`.
   **O nó do parâmetro** (`κ = 0`, a transição): `Parametro.pontes_parametro`, `Maquina.Q_kappa_zero`.
4. **Lacuna L5 fechada no modelo: a saturação além do quadrático** (`lombada4`, `quartica_fatora`,
   `quartica_par_fora`, `saturacao_superior`, `saturacao_inferior`). Na lombada quártica `(A − ε) − cx² + dx⁴`
   (`c, d > 0`), passado o limiar `ε > A` os zeros perto do centro são `±i·b` com
   `b² = (√(c² + 4d(ε − A)) − c)/(2d)`, e
   `(ε − A)/c − d(ε − A)²/c³ ≤ b² ≤ (ε − A)/c`: o termo quártico **satura** a lei da raiz quadrada, com correção de
   ordem `d(ε − A)²/c³`.
5. **Lacuna L6 fechada no modelo: empurrão ⟷ calor fora do par isolado** (`calor4`, `calor4_t`, `calor4_x`,
   `calor4_xx`, `calor4_equacao`, `calor4_inicio`, `calor4_centro`). Para a lombada quártica
   `f = A − cx² + dx⁴`, `H_t = f − t f'' + (t²/2) f''''` é solução **exata** de `∂ₜH = −∂²ₓH` (o fluxo de de Bruijn)
   com `H_0 = f`; no centro, `H_t(0) = A + 2ct + 12dt²`: voltar o tempo `|t|` é empurrar `|t|·|f''(0)| − (t²/2)f''''(0)`.

Nada aqui prova ou refuta RH; os problemas abertos continuam abertos. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Nos

open Complex ComplexConjugate

/-! ## 1. O nó do discriminante -/

/-- **Frobenius ⟺ círculo**: as raízes de `α² − λα + q` têm `|α|² = q` ⟺ as de `1 − λu + qu²` têm `|u|² = 1/q`. -/
theorem frobenius_iff_circulo {l q : ℝ} (hq : 0 < q) :
    (∀ α : ℂ, α ^ 2 - (l : ℂ) * α + (q : ℂ) = 0 → normSq α = q) ↔
      ∀ u : ℂ, 1 - (l : ℂ) * u + (q : ℂ) * u ^ 2 = 0 → normSq u = 1 / q := by
  have hq' : (q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hq.ne'
  constructor
  · intro h u hu
    have hu0 : u ≠ 0 := by
      rintro rfl
      norm_num at hu
    have hα : u⁻¹ ^ 2 - (l : ℂ) * u⁻¹ + (q : ℂ) = 0 := by
      have e : u⁻¹ ^ 2 - (l : ℂ) * u⁻¹ + (q : ℂ) = (1 - (l : ℂ) * u + (q : ℂ) * u ^ 2) / u ^ 2 := by
        field_simp
      rw [e, hu, zero_div]
    have := h _ hα
    rw [map_inv₀] at this
    rw [one_div, ← this, inv_inv]
  · intro h α hα
    have hα0 : α ≠ 0 := by
      rintro rfl
      norm_num at hα
      exact hq.ne' hα
    have hu : 1 - (l : ℂ) * α⁻¹ + (q : ℂ) * α⁻¹ ^ 2 = 0 := by
      have e : 1 - (l : ℂ) * α⁻¹ + (q : ℂ) * α⁻¹ ^ 2 = (α ^ 2 - (l : ℂ) * α + (q : ℂ)) / α ^ 2 := by
        field_simp
      rw [e, hα, zero_div]
    have := h _ hu
    rw [map_inv₀, one_div] at this
    exact inv_injective this

/-- **Todo `u ≠ 0` é `q^{−s}`** para `s = −log u/log q` (`q > 1`). -/
theorem todo_u_eh_potencia {q : ℝ} (hq : 1 < q) {u : ℂ} (hu : u ≠ 0) :
    ((q : ℂ) ^ (-(-Complex.log u / (Real.log q : ℂ)))) = u := by
  have hq0 : 0 < q := by linarith
  have hlog : (Real.log q : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.log_pos hq).ne'
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hq0.ne'), ← ofReal_log hq0.le, neg_div, neg_neg, mul_div_cancel₀ _ hlog,
    exp_log hu]

/-- **Reta ⟺ círculo**: os zeros de `1 − λq^{−s} + q(q^{−s})²` têm `Re s = ½` ⟺ os de `1 − λu + qu²` têm
`|u|² = 1/q` (`q > 1`). -/
theorem reta_iff_circulo {l q : ℝ} (hq : 1 < q) :
    (∀ s : ℂ, 1 - (l : ℂ) * (q : ℂ) ^ (-s) + (q : ℂ) * ((q : ℂ) ^ (-s)) ^ 2 = 0 → s.re = 1 / 2) ↔
      ∀ u : ℂ, 1 - (l : ℂ) * u + (q : ℂ) * u ^ 2 = 0 → normSq u = 1 / q := by
  constructor
  · intro h u hu
    have hu0 : u ≠ 0 := by
      rintro rfl
      norm_num at hu
    set s : ℂ := -Complex.log u / (Real.log q : ℂ)
    have hs : (q : ℂ) ^ (-s) = u := todo_u_eh_potencia hq hu0
    have hre := h s (by rw [hs]; exact hu)
    rw [← hs]
    exact (Geometrias.circulo_eh_reta hq s).mpr hre
  · intro h s hs
    exact (Geometrias.circulo_eh_reta hq s).mp (h _ hs)

/-- **O nó do discriminante**: discriminante, positividade, círculo, Frobenius e reta são a mesma afirmação. -/
theorem no_discriminante {l q : ℝ} (hq : 1 < q) :
    [l ^ 2 ≤ 4 * q,
      ∀ m n : ℝ, 0 ≤ m ^ 2 - l * m * n + q * n ^ 2,
      ∀ u : ℂ, 1 - (l : ℂ) * u + (q : ℂ) * u ^ 2 = 0 → normSq u = 1 / q,
      ∀ α : ℂ, α ^ 2 - (l : ℂ) * α + (q : ℂ) = 0 → normSq α = q,
      ∀ s : ℂ, 1 - (l : ℂ) * (q : ℂ) ^ (-s) + (q : ℂ) * ((q : ℂ) ^ (-s)) ^ 2 = 0 → s.re = 1 / 2].TFAE := by
  have hq0 : 0 < q := by linarith
  tfae_have 1 ↔ 2 := (Maquina.positividade_iff hq0).symm
  tfae_have 1 ↔ 3 := (Geometrias.circulo_iff hq0).symm
  tfae_have 3 ↔ 4 := (frobenius_iff_circulo hq0).symm
  tfae_have 3 ↔ 5 := (reta_iff_circulo hq).symm
  tfae_finish

/-! ## 2. O nó simetria = conjugação -/

/-- **A equação funcional local**: `P(1/(qu)) = P(u)/(qu²)` para `P(u) = 1 − λu + qu²` (o análogo de `s ↦ 1 − s`). -/
theorem equacao_funcional_local {l q : ℝ} (hq : q ≠ 0) {u : ℂ} (hu : u ≠ 0) :
    1 - (l : ℂ) * (1 / ((q : ℂ) * u)) + (q : ℂ) * (1 / ((q : ℂ) * u)) ^ 2 =
      (1 - (l : ℂ) * u + (q : ℂ) * u ^ 2) / ((q : ℂ) * u ^ 2) := by
  have hq' : (q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hq
  field_simp
  ring

/-- **Estar no círculo é o parceiro da equação funcional ser o conjugado**: `|u|² = 1/q ⟺ ū = 1/(qu)`. -/
theorem simetria_eh_conjugacao {q : ℝ} (hq : q ≠ 0) {u : ℂ} (hu : u ≠ 0) :
    normSq u = 1 / q ↔ conj u = 1 / ((q : ℂ) * u) := by
  have hq' : (q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hq
  rw [eq_div_iff (mul_ne_zero hq' hu)]
  constructor
  · intro h
    have e : conj u * ((q : ℂ) * u) = (q : ℂ) * (u * conj u) := by ring
    rw [e, mul_conj, h]
    push_cast
    field_simp
  · intro h
    have e : conj u * ((q : ℂ) * u) = (q : ℂ) * (u * conj u) := by ring
    rw [e, mul_conj] at h
    have h' : ((q * normSq u : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; exact h
    have h'' := ofReal_injective h'
    field_simp
    linarith

/-! ## 4. Lacuna L5: a saturação além do quadrático -/

/-- **A lombada quártica empurrada**: `(A − ε) − c·x² + d·x⁴`. -/
def lombada4 (A c d ε : ℝ) (x : ℂ) : ℂ := ((A - ε : ℝ) : ℂ) - (c : ℂ) * x ^ 2 + (d : ℂ) * x ^ 4

/-- **Fatoração em `y = x²`**: `4d·lombada4 = (2dx² − c − √D)(2dx² − c + √D)`, `D = c² − 4d(A − ε) ≥ 0`; os zeros
são `x² = (c ± √D)/(2d)`. -/
theorem quartica_fatora {A c d ε : ℝ} (hD : 0 ≤ c ^ 2 - 4 * d * (A - ε)) (x : ℂ) :
    4 * (d : ℂ) * lombada4 A c d ε x =
      (2 * (d : ℂ) * x ^ 2 - c - (Real.sqrt (c ^ 2 - 4 * d * (A - ε)) : ℂ)) *
        (2 * (d : ℂ) * x ^ 2 - c + (Real.sqrt (c ^ 2 - 4 * d * (A - ε)) : ℂ)) := by
  have hs' : ((Real.sqrt (c ^ 2 - 4 * d * (A - ε)) : ℝ) : ℂ) ^ 2 = ((c ^ 2 - 4 * d * (A - ε) : ℝ) : ℂ) := by
    rw [← ofReal_pow, Real.sq_sqrt hD]
  unfold lombada4
  push_cast at hs' ⊢
  linear_combination hs'

/-- **Passado o limiar, o par sai da reta**: com `c, d > 0` e `ε > A`, `x = i·√b²` é zero, com
`b² = (√(c² + 4d(ε − A)) − c)/(2d) > 0`. -/
theorem quartica_par_fora {A c d ε : ℝ} (hc : 0 < c) (hd : 0 < d) (hε : A < ε) :
    0 < (Real.sqrt (c ^ 2 + 4 * d * (ε - A)) - c) / (2 * d) ∧
      lombada4 A c d ε (I * (Real.sqrt ((Real.sqrt (c ^ 2 + 4 * d * (ε - A)) - c) / (2 * d)) : ℂ)) = 0 := by
  set S := Real.sqrt (c ^ 2 + 4 * d * (ε - A)) with hSdef
  have hS2 : S ^ 2 = c ^ 2 + 4 * d * (ε - A) := Real.sq_sqrt (by positivity)
  have hgt : c < S := by
    rw [hSdef, Real.lt_sqrt hc.le]
    nlinarith
  set b2 := (S - c) / (2 * d) with hb2def
  have hb2 : 0 < b2 := div_pos (by linarith) (by positivity)
  refine ⟨hb2, ?_⟩
  have hq : d * b2 ^ 2 + c * b2 + (A - ε) = 0 := by
    have e : d * b2 ^ 2 + c * b2 + (A - ε) = (S ^ 2 - (c ^ 2 + 4 * d * (ε - A))) / (4 * d) := by
      rw [hb2def]
      field_simp
      ring
    rw [e, hS2, sub_self, zero_div]
  have hb : ((Real.sqrt b2 : ℝ) : ℂ) ^ 2 = (b2 : ℂ) := by rw [← ofReal_pow, Real.sq_sqrt hb2.le]
  have e2 : (I * (Real.sqrt b2 : ℂ)) ^ 2 = -(b2 : ℂ) := by rw [mul_pow, I_sq, hb]; ring
  have e4 : (I * (Real.sqrt b2 : ℂ)) ^ 4 = (b2 : ℂ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, e2]
    ring
  unfold lombada4
  rw [e4, e2]
  have hq' := congrArg (fun r : ℝ => (r : ℂ)) hq
  push_cast at hq' ⊢
  linear_combination hq'

/-- **Saturação, cota superior**: `b² ≤ (ε − A)/c`: o termo quártico só freia a lei da raiz quadrada. -/
theorem saturacao_superior {A c d ε : ℝ} (hc : 0 < c) (hd : 0 < d) (hε : A < ε) :
    (Real.sqrt (c ^ 2 + 4 * d * (ε - A)) - c) / (2 * d) ≤ (ε - A) / c := by
  set S := Real.sqrt (c ^ 2 + 4 * d * (ε - A)) with hSdef
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = c ^ 2 + 4 * d * (ε - A) := Real.sq_sqrt (by positivity)
  have hh : 0 < ε - A := by linarith
  have key : c * S ≤ c ^ 2 + 2 * d * (ε - A) := by
    have h2 : (c * S) ^ 2 ≤ (c ^ 2 + 2 * d * (ε - A)) ^ 2 := by
      rw [mul_pow, hS2]
      nlinarith [sq_nonneg (d * (ε - A))]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h2
  rw [div_le_div_iff₀ (by positivity) hc]
  nlinarith [key]

/-- **Saturação, cota inferior**: `b² ≥ (ε − A)/c − d(ε − A)²/c³` (a correção é de ordem `d(ε − A)²/c³`). -/
theorem saturacao_inferior {A c d ε : ℝ} (hc : 0 < c) (hd : 0 < d) (hε : A < ε) :
    (ε - A) / c - d * (ε - A) ^ 2 / c ^ 3 ≤ (Real.sqrt (c ^ 2 + 4 * d * (ε - A)) - c) / (2 * d) := by
  set S := Real.sqrt (c ^ 2 + 4 * d * (ε - A)) with hSdef
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = c ^ 2 + 4 * d * (ε - A) := Real.sq_sqrt (by positivity)
  set h := ε - A with hhdef
  have hh : 0 < h := by rw [hhdef]; linarith
  have hc3 : 0 < c ^ 3 := by positivity
  set y := d * h with hydef
  have hy : 0 < y := by positivity
  set L := c ^ 4 + 2 * c ^ 2 * y - 2 * y ^ 2 with hLdef
  have key : L ≤ c ^ 3 * S := by
    by_cases hy2 : y ≤ 2 * c ^ 2
    · by_cases hL : L ≤ 0
      · exact le_trans hL (by positivity)
      · push Not at hL
        have h2 : L ^ 2 ≤ (c ^ 3 * S) ^ 2 := by
          rw [mul_pow, hS2, hLdef]
          have e : (c ^ 3) ^ 2 * (c ^ 2 + 4 * d * h) - (c ^ 4 + 2 * c ^ 2 * y - 2 * y ^ 2) ^ 2 =
              4 * y ^ 3 * (2 * c ^ 2 - y) := by
            rw [hydef]
            ring
          have : 0 ≤ 4 * y ^ 3 * (2 * c ^ 2 - y) := by
            apply mul_nonneg (by positivity)
            linarith
          linarith
        exact (pow_le_pow_iff_left₀ hL.le (by positivity) two_ne_zero).mp h2
    · push Not at hy2
      have : L < 0 := by
        rw [hLdef]
        nlinarith [hy2, sq_nonneg c]
      exact le_trans this.le (by positivity)
  have e1 : h / c - d * h ^ 2 / c ^ 3 = (c ^ 2 * h - d * h ^ 2) / c ^ 3 := by
    field_simp
  rw [e1, div_le_div_iff₀ hc3 (by positivity)]
  have e2 : c ^ 3 * (S - c) - 2 * d * (c ^ 2 * h - d * h ^ 2) = c ^ 3 * S - L := by
    rw [hLdef, hydef]
    ring
  nlinarith [key, e2]

/-! ## 5. Lacuna L6: o calor exato na lombada quártica -/

/-- **O fluxo de de Bruijn na lombada quártica**: `H_t(x) = f(x) − t f''(x) + (t²/2) f''''(x)` com
`f = A − cx² + dx⁴`: `H_t(x) = A − cx² + dx⁴ − t(−2c + 12dx²) + 12dt²`. -/
def calor4 (A c d t x : ℝ) : ℝ := A - c * x ^ 2 + d * x ^ 4 - t * (-2 * c + 12 * d * x ^ 2) + 12 * d * t ^ 2

/-- `H_0 = f`. -/
theorem calor4_inicio (A c d x : ℝ) : calor4 A c d 0 x = A - c * x ^ 2 + d * x ^ 4 := by
  unfold calor4
  ring

/-- `∂ₜH = 2c − 12dx² + 24dt`. -/
theorem calor4_t (A c d t x : ℝ) :
    HasDerivAt (fun s => calor4 A c d s x) (2 * c - 12 * d * x ^ 2 + 24 * d * t) t := by
  have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
  have h := ((hasDerivAt_const t (A - c * x ^ 2 + d * x ^ 4)).sub
    ((hasDerivAt_id t).mul_const (-2 * c + 12 * d * x ^ 2))).add (h2.const_mul (12 * d))
  exact h.congr_deriv (by simp; ring)

/-- `∂ₓH = −2cx + 4dx³ − 24dtx`. -/
theorem calor4_x (A c d t x : ℝ) :
    HasDerivAt (fun y => calor4 A c d t y) (-2 * c * x + 4 * d * x ^ 3 - 24 * d * t * x) x := by
  have p2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
  have p4 : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by simpa using hasDerivAt_pow 4 x
  have h := ((((hasDerivAt_const x A).sub (p2.const_mul c)).add (p4.const_mul d)).sub
    (((hasDerivAt_const x (-2 * c)).add (p2.const_mul (12 * d))).const_mul t)).add
    (hasDerivAt_const x (12 * d * t ^ 2))
  exact h.congr_deriv (by ring)

/-- `∂²ₓH = −2c + 12dx² − 24dt`. -/
theorem calor4_xx (c d t x : ℝ) :
    HasDerivAt (fun y => -2 * c * y + 4 * d * y ^ 3 - 24 * d * t * y) (-2 * c + 12 * d * x ^ 2 - 24 * d * t) x := by
  have p3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by simpa using hasDerivAt_pow 3 x
  have h := (((hasDerivAt_id x).const_mul (-2 * c)).add (p3.const_mul (4 * d))).sub
    ((hasDerivAt_id x).const_mul (24 * d * t))
  exact h.congr_deriv (by simp; ring)

/-- **A equação do calor de de Bruijn, exata**: `∂ₜH + ∂²ₓH = 0`. -/
theorem calor4_equacao (c d t x : ℝ) :
    (2 * c - 12 * d * x ^ 2 + 24 * d * t) + (-2 * c + 12 * d * x ^ 2 - 24 * d * t) = 0 := by
  ring

/-- **No centro**: `H_t(0) = A + 2ct + 12dt²`; voltar o tempo `|t|` é empurrar `2c|t| − 12dt²`
(`= |t|·|f''(0)| − (t²/2) f''''(0)`). -/
theorem calor4_centro (A c d t : ℝ) : calor4 A c d t 0 = A + 2 * c * t + 12 * d * t ^ 2 := by
  unfold calor4
  ring

end ClayRiemannProof.Nos
