import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# O "eixo Riemann": o que o kernel aceita e o que ele recusa

Proposta em teste: todo número vira `a + b·i + c·R`, com `a b c : ℝ`, `i² = -1`, `R² = R` e `i·R = R·i = R`.

## Resultados

* `R3.mul_comm`, `R3.one_mul`, `R3.exemplo_produto`: a tabuada proposta é comutativa, tem unidade e reproduz
  a conta `(5 + 2i + 0,1R)(3 + i + 0,2R) = 13 + 11i + 1,82R`.
* `R3.nao_associativa`: ela **não** é associativa: `(i·i)·R = -R`, mas `i·(i·R) = R`.
* `sem_raiz_de_menos_um_dim3`, `sem_algebra_associativa_dim3`: nenhuma tabuada resolve isso. Em qualquer
  multiplicação associativa com unidade em `ℝ³`, nenhum elemento tem quadrado `-1`. Motivo: `L = (i · _)`
  teria `L ∘ L = -id`, e então `det(L)² = det(-id) = (-1)³ = -1`.
* `Dual`, `Idem`: as duas versões consistentes têm 4 componentes, porque o coeficiente da cauda também é
  complexo. `Dual` (`ε² = 0`, cauda de cauda some, como Taylor de 1ª ordem) e `Idem` (`e² = e`, absorvente)
  são associativas e comutativas.
* `decomposicao_vale_sempre`, `decomposicao_nao_exclui_zeros`, `zero_fora_vira_cauda`: a decomposição
  `f(s) = f(s puxado) + I` vale para qualquer função e qualquer ponto, inclusive para funções com zero fora da
  reta. Ela não exclui zeros: um zero fora da reta de ζ apareceria só como `I_ζ(ρ) = -ζ(1/2 + i·Im ρ)`.
-/

namespace EixoRiemann

/-! ## 1. A tabuada proposta, com 3 componentes reais -/

@[ext] structure R3 where
  re : ℝ
  im : ℝ
  r : ℝ

namespace R3

instance : Mul R3 where
  mul x y := ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re,
    x.re * y.r + x.r * y.re + x.r * y.r + x.im * y.r + x.r * y.im⟩

instance : One R3 := ⟨⟨1, 0, 0⟩⟩

@[simp] theorem mul_re (x y : R3) : (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp] theorem mul_im (x y : R3) : (x * y).im = x.re * y.im + x.im * y.re := rfl
@[simp] theorem mul_r (x y : R3) :
    (x * y).r = x.re * y.r + x.r * y.re + x.r * y.r + x.im * y.r + x.r * y.im := rfl

/-- `i = 0 + 1·i + 0·R` e `R = 0 + 0·i + 1·R`. -/
def i : R3 := ⟨0, 1, 0⟩
def R : R3 := ⟨0, 0, 1⟩

theorem i_mul_i : i * i = ⟨-1, 0, 0⟩ := by ext <;> simp [i]
theorem R_mul_R : R * R = R := by ext <;> simp [R]
theorem i_mul_R : i * R = R := by ext <;> simp [i, R]

theorem mul_comm (x y : R3) : x * y = y * x := by ext <;> simp <;> ring
theorem one_mul (x : R3) : 1 * x = x := by ext <;> simp [show (1 : R3) = ⟨1, 0, 0⟩ from rfl]

/-- Habitante: a conta do exemplo, `(5 + 2i + 0,1R)(3 + i + 0,2R) = 13 + 11i + 1,82R`. -/
theorem exemplo_produto :
    (⟨5, 2, 1/10⟩ : R3) * ⟨3, 1, 2/10⟩ = ⟨13, 11, 182/100⟩ := by ext <;> simp <;> norm_num

/-- **A tabuada proposta não é associativa:** `(i·i)·R = -R` e `i·(i·R) = R`. -/
theorem nao_associativa : (i * i) * R ≠ i * (i * R) := by
  intro h
  have := congrArg R3.r h
  simp [i, R] at this
  norm_num at this

end R3

/-! ## 2. Nenhuma tabuada com 3 componentes reais funciona -/

/-- Em `ℝ³`, nenhuma aplicação linear tem quadrado `-id`: `det(L)² ≥ 0`, mas `det(-id) = -1`. -/
theorem sem_raiz_de_menos_um_dim3 (L : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) :
    L.comp L ≠ -LinearMap.id := by
  intro h
  have h1 := congrArg LinearMap.det h
  rw [LinearMap.det_comp] at h1
  have h2 : LinearMap.det (-LinearMap.id : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) = -1 := by
    rw [show (-LinearMap.id : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) = (-1 : ℝ) • LinearMap.id from
      (neg_one_smul ℝ _).symm, LinearMap.det_smul, Module.finrank_fin_fun ℝ, LinearMap.det_id]
    norm_num
  rw [h2] at h1
  nlinarith [mul_self_nonneg (LinearMap.det L)]

/-- **Inabitante:** não existe multiplicação bilinear, associativa e com unidade em `ℝ³` com um `i` tal que
`i·i = -1`. Vale para qualquer tabuada do terceiro eixo, não só para `R² = R`, `i·R = R`. -/
theorem sem_algebra_associativa_dim3 (mul : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
    (one i : Fin 3 → ℝ) (h_one : ∀ x, mul one x = x)
    (h_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)) (h_i : mul i i = -one) : False := by
  apply sem_raiz_de_menos_um_dim3 (mul i)
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, LinearMap.neg_apply, LinearMap.id_apply]
  rw [← h_assoc, h_i, map_neg, LinearMap.neg_apply, h_one]

/-! ## 3. As versões consistentes têm 4 componentes: a cauda também é complexa -/

/-- `z + w·ε` com `ε² = 0`: a cauda de cauda some (Taylor de primeira ordem). -/
@[ext] structure Dual where
  z : ℂ
  w : ℂ

instance : Mul Dual := ⟨fun x y => ⟨x.z * y.z, x.z * y.w + x.w * y.z⟩⟩

@[simp] theorem Dual.mul_z (x y : Dual) : (x * y).z = x.z * y.z := rfl
@[simp] theorem Dual.mul_w (x y : Dual) : (x * y).w = x.z * y.w + x.w * y.z := rfl

theorem Dual.mul_assoc (x y t : Dual) : (x * y) * t = x * (y * t) := by
  ext <;> simp <;> ring

theorem Dual.mul_comm (x y : Dual) : x * y = y * x := by
  ext <;> simp <;> ring

/-- `z + w·e` com `e² = e`: a cauda absorve, como o 𝕀. -/
@[ext] structure Idem where
  z : ℂ
  w : ℂ

instance : Mul Idem := ⟨fun x y => ⟨x.z * y.z, x.z * y.w + x.w * y.z + x.w * y.w⟩⟩

@[simp] theorem Idem.mul_z (x y : Idem) : (x * y).z = x.z * y.z := rfl
@[simp] theorem Idem.mul_w (x y : Idem) : (x * y).w = x.z * y.w + x.w * y.z + x.w * y.w := rfl

theorem Idem.mul_assoc (x y t : Idem) : (x * y) * t = x * (y * t) := by
  ext <;> simp <;> ring

theorem Idem.e_mul_e : (⟨0, 1⟩ : Idem) * ⟨0, 1⟩ = ⟨0, 1⟩ := by
  ext <;> simp

/-- Em `Idem`, `i·e` é `i·e`, um ponto próprio do eixo, e não `e`: é isso que salva a associatividade. -/
theorem Idem.i_mul_e : (⟨Complex.I, 0⟩ : Idem) * ⟨0, 1⟩ = ⟨0, Complex.I⟩ := by
  ext <;> simp

/-! ## 4. "Puxar para a reta" não decide nada sobre os zeros -/

/-- O ponto puxado: mesma parte imaginária, parte real 1/2. -/
noncomputable def puxado (s : ℂ) : ℂ := 1 / 2 + (s.im : ℂ) * Complex.I

/-- `I_f(s) = f(s) - f(s puxado)`. -/
noncomputable def cauda (f : ℂ → ℂ) (s : ℂ) : ℂ := f s - f (puxado s)

/-- **Incondicional:** `f(s) = f(s puxado) + I_f(s)` vale para qualquer função e qualquer ponto. É álgebra. -/
theorem decomposicao_vale_sempre (f : ℂ → ℂ) (s : ℂ) : f s = f (puxado s) + cauda f s := by
  unfold cauda; ring

/-- **Contraexemplo:** a decomposição vale também para `f(s) = s - 1`, que tem zero em `s = 1`, fora da reta
`Re s = 1/2`. Então "vale a decomposição" não implica "todos os zeros estão na reta". -/
theorem decomposicao_nao_exclui_zeros :
    ¬ ∀ f : ℂ → ℂ, (∀ s, f s = f (puxado s) + cauda f s) → ∀ s, f s = 0 → s.re = 1 / 2 := by
  intro h
  have := h (fun s => s - 1) (decomposicao_vale_sempre _) 1 (by simp)
  norm_num at this

/-- **Condicional:** se `ζ` tivesse um zero `ρ` fora da reta, a decomposição continuaria valendo nele; o zero
apareceria só como `I_ζ(ρ) = -ζ(1/2 + i·Im ρ)`. A representação acomoda o zero; não o impede. -/
theorem zero_fora_vira_cauda (ρ : ℂ) (h : riemannZeta ρ = 0) :
    cauda riemannZeta ρ = -riemannZeta (puxado ρ) := by
  unfold cauda; rw [h]; ring

end EixoRiemann

#print axioms EixoRiemann.R3.nao_associativa
#print axioms EixoRiemann.R3.exemplo_produto
#print axioms EixoRiemann.sem_algebra_associativa_dim3
#print axioms EixoRiemann.Dual.mul_assoc
#print axioms EixoRiemann.Idem.mul_assoc
#print axioms EixoRiemann.decomposicao_nao_exclui_zeros
#print axioms EixoRiemann.zero_fora_vira_cauda
