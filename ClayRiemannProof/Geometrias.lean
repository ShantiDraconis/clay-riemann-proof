import ClayRiemannProof.QuartetoForcado

/-!
# As geometrias onde a RH é provada e onde ela falha: uma só ponte, a do discriminante

Em toda família de funções zeta que tem "RH", a hipótese vira uma cota de discriminante numa equação de grau 2:

| família | fator local | RH ⟺ | situação |
|---|---|---|---|
| curva elíptica `E/𝔽_q` | `1 − a·u + q·u²`, `u = q^{−s}` | `a² ≤ 4q` (Hasse) | **provada** (Hasse 1933, Weil 1948, Deligne 1974) |
| grafo `(q+1)`-regular (zeta de Ihara) | `1 − λ·u + q·u²` por autovalor não trivial | `λ² ≤ 4q` (Ramanujan) | vale para alguns grafos, falha para outros |
| superfície hiperbólica (zeta de Selberg) | `s(1 − s) = λ` por autovalor do laplaciano | `λ ≥ ¼` | falha se há `λ < ¼`; aberta para grupos de congruência |
| modelo local de ζ (`Parametro`) | `(w − iγ₀)² + κ` | `κ ≥ 0` | aberta (é a própria RH) |
| só a equação funcional (Davenport–Heilbronn, Epstein) | nenhum | — | **falha** (`Analogs.simetria_nao_basta_abstrata`, README §34, §39) |

Este arquivo prova a ponte e a verifica nas geometrias concretas:

1. **A ponte** (`circulo_iff`): as raízes de `1 − λu + qu²` (`q > 0`) estão todas em `|u|² = 1/q` ⟺ `λ² ≤ 4q`; e
   `|q^{−s}|² = 1/q` ⟺ `Re s = ½` (`circulo_eh_reta`, `q > 1`). O círculo de raio `q^{−1/2}` **é** a reta crítica.
2. **Curvas elípticas: a RH provada no kernel, curva por curva** (`hasse_F5`, `hasse_F7`, `hasse_F11`,
   `hasse_F13`, `rh_curva`, `rh_curva_reta`, `hasse_justo`). Para **todas** as curvas `y² = x³ + ax + b` sobre
   `𝔽₅, 𝔽₇, 𝔽₁₁, 𝔽₁₃` (20, 42, 110 e 156 curvas), o traço `a_p = p − #{(x, y)}` satisfaz `a_p² ≤ 4p`, contado por
   `decide`; logo os zeros de `1 − a_p p^{−s} + p^{1−2s}` estão em `Re s = ½`. O valor `#E = p + 1 − a_p` e a
   identidade `Z(E, u) = (1 − a_p u + pu²)/((1 − u)(1 − pu))` são o teorema de Hasse–Weil, não formalizado aqui; o
   que o kernel confere é a cota em cada curva.
3. **Grafos: uma geometria que prova e uma que refuta** (`Ramanujan`, `ramanujan_iff_circulo`, `petersen_ramanujan`,
   `prisma_nao_ramanujan`, `prisma_zeros_fora`). O grafo de Petersen (3-regular, `q = 2`) tem `A² + A − 2I = J`,
   então todo autovalor não trivial é `1` ou `−2`, com `λ² ≤ 8`: Ramanujan, RH de Ihara. O prisma `K₇ □ K₂`
   (7-regular, `q = 6`) tem o autovalor não trivial `5`, com `25 > 24`: o fator `1 − 5u + 6u² = (1 − 2u)(1 − 3u)`
   tem zeros `u = ½` e `u = ⅓`, fora do círculo `|u|² = 1/6`; em `u = 6^{−s}` são `s = log 2/log 6` e
   `log 3/log 6`, simétricos em torno de `½` e fora da reta. O fator é o da fórmula de Ihara–Bass (Ihara 1966,
   Bass 1992), citada, não formalizada.
4. **Selberg: o parâmetro é `λ − ¼`** (`selberg_eh_kappa`, `selberg_reta`, `desvio_de_lambda`, `selberg_316`,
   `kim_sarnak`). `s(1 − s) = λ` ⟺ `(s − ½)² + (λ − ¼) = 0`, a mesma forma do `QuartetoForcado.Q` com
   `κ = λ − ¼`. Na reta exatamente para `λ ≥ ¼`; com `λ ≥ ¼ − b²` o desvio é `≤ b`. A cota de Selberg `3/16` dá
   desvio `≤ ¼`; a de Kim–Sarnak `975/4096` dá `≤ 7/64` (as cotas são teoremas publicados; aqui só a álgebra).

**O que isto não é**: nenhuma destas geometrias é ζ. Para as curvas a RH sai de um operador (Frobenius) cujos
autovalores têm módulo `√q`; para ζ esse operador não é conhecido (Hilbert–Pólya), e a cota de discriminante
correspondente é a própria RH (`Parametro.pontes_parametro`, `LiCircle.target_iff_ramanujan`). Nada aqui prova ou
refuta RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Geometrias

open Complex

/-! ## 1. A ponte: o círculo `|u|² = 1/q` e a reta `Re s = ½` -/

/-- **A ponte do discriminante**: todas as raízes de `1 − λu + qu²` (`q > 0`) estão no círculo `|u|² = 1/q` se e só
se `λ² ≤ 4q`. -/
theorem circulo_iff {l q : ℝ} (hq : 0 < q) :
    (∀ u : ℂ, 1 - (l : ℂ) * u + (q : ℂ) * u ^ 2 = 0 → normSq u = 1 / q) ↔ l ^ 2 ≤ 4 * q := by
  constructor
  · intro h
    by_contra hlt
    have hD : 0 < l ^ 2 - 4 * q := by linarith [lt_of_not_ge hlt]
    set r := Real.sqrt (l ^ 2 - 4 * q) with hr
    have hsq : r ^ 2 = l ^ 2 - 4 * q := Real.sq_sqrt hD.le
    set x : ℝ := (l + r) / (2 * q) with hx
    have hroot : 1 - l * x + q * x ^ 2 = 0 := by
      have e : 1 - l * x + q * x ^ 2 = (r ^ 2 - (l ^ 2 - 4 * q)) / (4 * q) := by
        rw [hx]
        field_simp
        ring
      rw [e, hsq, sub_self, zero_div]
    have hu := h (x : ℂ) (by
      have e := congrArg (fun y : ℝ => (y : ℂ)) hroot
      push_cast at e
      linear_combination e)
    rw [normSq_ofReal] at hu
    have h1 : q * (x * x) = 1 := by
      rw [hu]
      field_simp
    have h2 : l * x = 2 := by nlinarith [hroot, h1]
    have h3 : l ^ 2 * (x * x) = 4 := by nlinarith [h2]
    rw [hu] at h3
    have h4 : l ^ 2 = 4 * q := by
      field_simp at h3
      linarith
    linarith
  · intro hl u hu
    have hre := congrArg Complex.re hu
    have him := congrArg Complex.im hu
    simp only [sub_re, add_re, one_re, mul_re, ofReal_re, ofReal_im, pow_two, sub_im, add_im, one_im, mul_im,
      zero_re, zero_im, zero_mul, sub_zero, add_zero] at hre him
    rw [normSq_apply]
    have hfac : u.im * (2 * q * u.re - l) = 0 := by linarith
    have hb : 2 * q * u.re = l := by
      rcases mul_eq_zero.mp hfac with h0 | h0
      · rw [h0] at hre
        have ha : (2 * q * u.re - l) ^ 2 + (4 * q - l ^ 2) = 0 := by nlinarith [hre]
        have hc : (2 * q * u.re - l) ^ 2 = 0 := by nlinarith [sq_nonneg (2 * q * u.re - l)]
        have hd := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp hc
        linarith
      · linarith
    have key : q * (u.re * u.re + u.im * u.im) = 1 := by linear_combination u.re * hb - hre
    field_simp
    linarith

/-- **O círculo é a reta**: para `q > 1`, `|q^{−s}|² = 1/q` ⟺ `Re s = ½`. -/
theorem circulo_eh_reta {q : ℝ} (hq : 1 < q) (s : ℂ) : normSq ((q : ℂ) ^ (-s)) = 1 / q ↔ s.re = 1 / 2 := by
  have hq0 : 0 < q := by linarith
  rw [normSq_eq_norm_sq, norm_cpow_eq_rpow_re_of_pos hq0, neg_re, ← Real.rpow_natCast,
    ← Real.rpow_mul hq0.le, one_div, ← Real.rpow_neg_one, Real.rpow_right_inj hq0 hq.ne']
  constructor <;> intro h <;> push_cast at * <;> linarith

/-! ## 2. Curvas elípticas sobre `𝔽_p`: a RH provada curva por curva -/

/-- Pontos afins de `y² = x³ + ax + b` sobre `𝔽_p` (`0 ≤ x, y < p`, contagem exata). -/
def pontosAfins (p a b : ℕ) : ℕ :=
  ((List.range p).flatMap fun x => (List.range p).map fun y => (x, y)).countP
    fun xy => (xy.2 * xy.2) % p == (xy.1 * xy.1 * xy.1 + a * xy.1 + b) % p

/-- O traço de Frobenius `a_p = p + 1 − #E(𝔽_p)`, com `#E` = pontos afins + o ponto no infinito. -/
def traco (p a b : ℕ) : ℤ := (p : ℤ) + 1 - ((pontosAfins p a b : ℤ) + 1)

/-- **Hasse sobre `𝔽₅`**: as 20 curvas não singulares têm `a² ≤ 20`. -/
theorem hasse_F5 : ∀ a < 5, ∀ b < 5, (4 * a ^ 3 + 27 * b ^ 2) % 5 ≠ 0 → traco 5 a b ^ 2 ≤ 4 * 5 := by
  decide +kernel

/-- **Hasse sobre `𝔽₇`**: as 42 curvas não singulares têm `a² ≤ 28`. -/
theorem hasse_F7 : ∀ a < 7, ∀ b < 7, (4 * a ^ 3 + 27 * b ^ 2) % 7 ≠ 0 → traco 7 a b ^ 2 ≤ 4 * 7 := by
  decide +kernel

/-- **Hasse sobre `𝔽₁₁`**: as 110 curvas não singulares têm `a² ≤ 44`. -/
theorem hasse_F11 : ∀ a < 11, ∀ b < 11, (4 * a ^ 3 + 27 * b ^ 2) % 11 ≠ 0 → traco 11 a b ^ 2 ≤ 4 * 11 := by
  decide +kernel

/-- **Hasse sobre `𝔽₁₃`**: as 156 curvas não singulares têm `a² ≤ 52`. -/
theorem hasse_F13 : ∀ a < 13, ∀ b < 13, (4 * a ^ 3 + 27 * b ^ 2) % 13 ≠ 0 → traco 13 a b ^ 2 ≤ 4 * 13 := by
  decide +kernel

/-- **A cota é justa**: sobre `𝔽₁₃` há curva com `a² = 49`, a um passo de `4p = 52`. -/
theorem hasse_justo : ∃ a < 13, ∃ b < 13, (4 * a ^ 3 + 27 * b ^ 2) % 13 ≠ 0 ∧ traco 13 a b ^ 2 = 49 := by
  decide +kernel

/-- **RH da curva**: da cota de Hasse, os zeros de `1 − a_p u + pu²` estão em `|u|² = 1/p`. -/
theorem rh_curva {p a b : ℕ} (hp : 0 < p) (h : traco p a b ^ 2 ≤ 4 * p) :
    ∀ u : ℂ, 1 - ((traco p a b : ℝ) : ℂ) * u + ((p : ℝ) : ℂ) * u ^ 2 = 0 → normSq u = 1 / p :=
  (circulo_iff (by exact_mod_cast hp)).mpr (by exact_mod_cast h)

/-- **RH da curva, na variável `s`**: os zeros de `1 − a_p p^{−s} + p·p^{−2s}` têm `Re s = ½`. -/
theorem rh_curva_reta {p a b : ℕ} (hp : 1 < p) (h : traco p a b ^ 2 ≤ 4 * p) (s : ℂ)
    (hs : 1 - ((traco p a b : ℝ) : ℂ) * ((p : ℝ) : ℂ) ^ (-s) + ((p : ℝ) : ℂ) * (((p : ℝ) : ℂ) ^ (-s)) ^ 2 = 0) :
    s.re = 1 / 2 :=
  (circulo_eh_reta (by exact_mod_cast hp) s).mp (rh_curva (by omega) h _ hs)

/-- **Todas as curvas sobre `𝔽₁₃` satisfazem a RH** (na variável `s`). -/
theorem rh_todas_F13 (a b : ℕ) (ha : a < 13) (hb : b < 13) (hd : (4 * a ^ 3 + 27 * b ^ 2) % 13 ≠ 0) (s : ℂ)
    (hs : 1 - ((traco 13 a b : ℝ) : ℂ) * ((13 : ℕ) : ℝ) ^ (-s) + ((13 : ℕ) : ℝ) * ((((13 : ℕ) : ℝ) : ℂ) ^ (-s)) ^ 2 = 0) :
    s.re = 1 / 2 :=
  rh_curva_reta (by norm_num) (hasse_F13 a ha b hb hd) s (by exact_mod_cast hs)

/-! ## 3. Grafos: a zeta de Ihara -/

/-- **Ramanujan (RH de Ihara)** para um grafo `(q+1)`-regular de matriz `A`: todo autovalor não trivial (autovetor
ortogonal ao vetor constante) tem `λ² ≤ 4q`. -/
def Ramanujan {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (q : ℝ) : Prop :=
  ∀ (l : ℝ) (v : Fin n → ℝ), v ≠ 0 → ∑ i, v i = 0 → A.mulVec v = l • v → l ^ 2 ≤ 4 * q

/-- **Ramanujan ⟺ os fatores de Ihara `1 − λu + qu²` têm os zeros no círculo `|u|² = 1/q`.** -/
theorem ramanujan_iff_circulo {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) {q : ℝ} (hq : 0 < q) :
    Ramanujan A q ↔ ∀ (l : ℝ) (v : Fin n → ℝ), v ≠ 0 → ∑ i, v i = 0 → A.mulVec v = l • v →
      ∀ u : ℂ, 1 - (l : ℂ) * u + (q : ℂ) * u ^ 2 = 0 → normSq u = 1 / q := by
  unfold Ramanujan
  exact forall_congr' fun l => forall_congr' fun v => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => (circulo_iff hq).symm

/-- Os 10 vértices do grafo de Petersen: os pares de `{0, …, 4}`; adjacentes ⟺ disjuntos. -/
def petersenPar : Fin 10 → ℕ × ℕ := ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

/-- Adjacência do grafo de Petersen. -/
def petersenAdj (i j : Fin 10) : ℤ :=
  if (petersenPar i).1 ≠ (petersenPar j).1 ∧ (petersenPar i).1 ≠ (petersenPar j).2 ∧
      (petersenPar i).2 ≠ (petersenPar j).1 ∧ (petersenPar i).2 ≠ (petersenPar j).2 then 1 else 0

/-- **Petersen é 3-regular.** -/
theorem petersen_regular : ∀ i : Fin 10, ∑ k, petersenAdj i k = 3 := by
  decide +kernel

/-- **`A² + A − 2I = J`** (grafo fortemente regular `(10, 3, 0, 1)`). -/
theorem petersen_quadrado :
    ∀ i j : Fin 10, (∑ k, petersenAdj i k * petersenAdj k j) + petersenAdj i j - 2 * (if i = j then 1 else 0) = 1 := by
  decide +kernel

/-- A matriz de Petersen em `ℝ`. -/
def petersen : Matrix (Fin 10) (Fin 10) ℝ := fun i j => (petersenAdj i j : ℝ)

/-- **Petersen é Ramanujan** (`q = 2`): os autovalores não triviais são `1` e `−2`, com `λ² ≤ 4 < 8`. -/
theorem petersen_ramanujan : Ramanujan petersen 2 := by
  intro l v hv hsum hA
  have hPP : ∀ i j, (petersen * petersen) i j = 1 - petersen i j + 2 * (if i = j then 1 else 0) := by
    intro i j
    have h := congrArg (fun z : ℤ => (z : ℝ)) (petersen_quadrado i j)
    simp only [Matrix.mul_apply, petersen]
    push_cast at h
    split_ifs at h ⊢ <;> linarith
  have hA2 : (petersen * petersen).mulVec v = (l * l) • v := by
    rw [← Matrix.mulVec_mulVec, hA, Matrix.mulVec_smul, hA, smul_smul]
  have hcoord : ∀ i, (l * l) * v i = ∑ j, v j - l * v i + 2 * v i := by
    intro i
    have e1 := congrFun hA2 i
    have e2 := congrFun hA i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at e1 e2
    rw [← e1]
    simp only [hPP, sub_mul, add_mul, one_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_assoc,
      ← Finset.mul_sum, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [e2]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  simp only [Pi.zero_apply] at hi
  have hl : (l * l + l - 2) * v i = 0 := by
    have := hcoord i
    rw [hsum] at this
    linarith
  have hl2 : l * l + l - 2 = 0 := (mul_eq_zero.mp hl).resolve_right hi
  nlinarith [sq_nonneg (l + 1 / 2)]

/-- Adjacência do prisma `K₇ □ K₂`: vértice `i = r + 7c`; adjacentes se mesma camada `c` (o `K₇`) ou mesmo `r` (a
aresta do `K₂`). -/
def prismaAdj (i j : Fin 14) : ℤ :=
  if i ≠ j ∧ (i.val / 7 = j.val / 7 ∨ i.val % 7 = j.val % 7) then 1 else 0

/-- **O prisma é 7-regular.** -/
theorem prisma_regular : ∀ i : Fin 14, ∑ k, prismaAdj i k = 7 := by
  decide +kernel

/-- O autovetor `+1` numa camada e `−1` na outra. -/
def prismaVetorZ (i : Fin 14) : ℤ := if i.val < 7 then 1 else -1

/-- **`A·w = 5w`**: o autovalor não trivial `5`. -/
theorem prisma_autovalor : ∀ i : Fin 14, ∑ k, prismaAdj i k * prismaVetorZ k = 5 * prismaVetorZ i := by
  decide +kernel

/-- A matriz do prisma em `ℝ`. -/
def prisma : Matrix (Fin 14) (Fin 14) ℝ := fun i j => (prismaAdj i j : ℝ)

/-- **O prisma `K₇ □ K₂` não é Ramanujan** (`q = 6`): o autovalor não trivial `5` tem `25 > 24`. -/
theorem prisma_nao_ramanujan : ¬ Ramanujan prisma 6 := by
  intro h
  have hw := h 5 (fun i => (prismaVetorZ i : ℝ)) ?_ ?_ ?_
  · norm_num at hw
  · intro h0
    have := congrFun h0 0
    simp [prismaVetorZ] at this
  · have : ∑ i, prismaVetorZ i = 0 := by decide
    exact_mod_cast this
  · funext i
    have e := congrArg (fun z : ℤ => (z : ℝ)) (prisma_autovalor i)
    simp only [Matrix.mulVec, dotProduct, prisma, Pi.smul_apply, smul_eq_mul]
    push_cast at e
    exact e

/-- **Os zeros de Ihara do prisma fora da reta**: `1 − 5u + 6u² = (1 − 2u)(1 − 3u)`, zeros `u = ½` e `u = ⅓` fora
de `|u|² = 1/6`; em `u = 6^{−s}`, `s₁ = log 2/log 6` e `s₂ = log 3/log 6`, com `s₁ + s₂ = 1` e `s₁ < ½`. -/
theorem prisma_zeros_fora :
    (∀ u : ℂ, 1 - 5 * u + 6 * u ^ 2 = (1 - 2 * u) * (1 - 3 * u)) ∧
      normSq (1 / 2 : ℂ) ≠ 1 / 6 ∧ normSq (1 / 3 : ℂ) ≠ 1 / 6 ∧
      (6 : ℝ) ^ (-(Real.log 2 / Real.log 6)) = 1 / 2 ∧ (6 : ℝ) ^ (-(Real.log 3 / Real.log 6)) = 1 / 3 ∧
      Real.log 2 / Real.log 6 + Real.log 3 / Real.log 6 = 1 ∧ Real.log 2 / Real.log 6 < 1 / 2 := by
  have h6 : (0 : ℝ) < Real.log 6 := Real.log_pos (by norm_num)
  have hlog : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have h23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  refine ⟨fun u => by ring, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [normSq_apply]
    norm_num
  · rw [normSq_apply]
    norm_num
  · rw [Real.rpow_def_of_pos (by norm_num), mul_neg, mul_div_cancel₀ _ h6.ne', Real.exp_neg,
      Real.exp_log (by norm_num)]
    norm_num
  · rw [Real.rpow_def_of_pos (by norm_num), mul_neg, mul_div_cancel₀ _ h6.ne', Real.exp_neg,
      Real.exp_log (by norm_num)]
    norm_num
  · rw [← add_div, ← hlog, div_self h6.ne']
  · rw [div_lt_iff₀ h6, hlog]
    linarith

/-! ## 4. Selberg: o parâmetro é `λ − ¼` -/

/-- **`s(1 − s) = λ` ⟺ `(s − ½)² + (λ − ¼) = 0`**: a forma do `QuartetoForcado.Q` com `κ = λ − ¼`. -/
theorem selberg_eh_kappa (l : ℝ) (s : ℂ) :
    s * (1 - s) = l ↔ (s - 1 / 2) ^ 2 + ((l - 1 / 4 : ℝ) : ℂ) = 0 := by
  push_cast
  constructor <;> intro h <;> linear_combination -h

/-- **Selberg: na reta exatamente para `λ ≥ ¼`.** Com `λ < ¼` (autovalor excepcional), `s = ½ + √(¼ − λ)` é um
zero fora da reta. -/
theorem selberg_reta (l : ℝ) : (∀ s : ℂ, s * (1 - s) = l → s.re = 1 / 2) ↔ 1 / 4 ≤ l := by
  constructor
  · intro h
    by_contra hl
    have hl' : l < 1 / 4 := lt_of_not_ge hl
    have hpos : 0 < 1 / 4 - l := by linarith
    have hsq : ((Real.sqrt (1 / 4 - l) : ℝ) : ℂ) ^ 2 = ((1 / 4 - l : ℝ) : ℂ) := by
      rw [← ofReal_pow, Real.sq_sqrt hpos.le]
    have := h (1 / 2 + (Real.sqrt (1 / 4 - l) : ℂ)) (by
      have e : (1 / 2 + (Real.sqrt (1 / 4 - l) : ℂ)) * (1 - (1 / 2 + (Real.sqrt (1 / 4 - l) : ℂ))) =
          1 / 4 - ((Real.sqrt (1 / 4 - l) : ℝ) : ℂ) ^ 2 := by ring
      rw [e, hsq]
      push_cast
      ring)
    simp only [add_re, ofReal_re, div_ofNat_re, one_re] at this
    have := Real.sqrt_pos.mpr hpos
    linarith
  · intro hl s hs
    have h := QuartetoForcado.quadrado_neg_re (z := s - 1 / 2) (κ := l - 1 / 4) (by linarith)
      ((selberg_eh_kappa l s).mp hs)
    simp only [sub_re, div_ofNat_re, one_re] at h
    linarith

/-- **O desvio controlado por `λ`**: se `λ ≥ ¼ − b²` (`b ≥ 0`), todo `s` com `s(1 − s) = λ` tem `|Re s − ½| ≤ b`. -/
theorem desvio_de_lambda {l b : ℝ} (hb : 0 ≤ b) (h : 1 / 4 - b ^ 2 ≤ l) (s : ℂ) (hs : s * (1 - s) = l) :
    |s.re - 1 / 2| ≤ b := by
  have hw : (s - 1 / 2) ^ 2 = ((1 / 4 - l : ℝ) : ℂ) := by
    push_cast
    linear_combination -hs
  have hre := congrArg Complex.re hw
  have him := congrArg Complex.im hw
  simp only [pow_two, mul_re, mul_im, sub_re, sub_im, div_ofNat_re, div_ofNat_im, one_re, one_im, ofReal_re,
    ofReal_im] at hre him
  have hx : (s.re - 1 / 2) * s.im = 0 := by nlinarith [him]
  rcases mul_eq_zero.mp hx with h0 | h0
  · rw [h0, abs_zero]
    exact hb
  · rw [h0] at hre
    apply abs_le_of_sq_le_sq _ hb
    nlinarith [hre]

/-- **Cota de Selberg (`λ₁ ≥ 3/16`)**: desvio `≤ ¼`. -/
theorem selberg_316 {l : ℝ} (h : 3 / 16 ≤ l) (s : ℂ) (hs : s * (1 - s) = l) : |s.re - 1 / 2| ≤ 1 / 4 :=
  desvio_de_lambda (by norm_num) (by norm_num; linarith) s hs

/-- **Cota de Kim–Sarnak (`λ₁ ≥ 975/4096`)**: desvio `≤ 7/64`. -/
theorem kim_sarnak {l : ℝ} (h : 975 / 4096 ≤ l) (s : ℂ) (hs : s * (1 - s) = l) : |s.re - 1 / 2| ≤ 7 / 64 :=
  desvio_de_lambda (by norm_num) (by norm_num; linarith) s hs

end ClayRiemannProof.Geometrias
