import ClayRiemannProof.EixoRiemann.Mapa

/-!
# Três valores: início fechado, fim fechado, meio

`V3 = {F, U, T}`: falso, intermediário (indeterminado), verdadeiro. Conectivos de Kleene (`e`, `ou`, `nao`),
implicação de Łukasiewicz (`impL`) e de Kleene (`impK`), e a versão de Bochvar (`eB`, `ouB`), onde `U` é absorvente
como o `𝕀 = 0/0`.

## As três codificações em `{0, 1, 2}`
* `codA`: `0 = F, 1 = T, 2 = U`. * `codB`: `0 = F, 1 = U, 2 = T`. * `codC`: `0 = T, 1 = U, 2 = F`.
* `codA_eq`, `codC_eq`: `codA` é `codB` com `1 ↔ 2` trocados; `codC` é `codB` invertida (`x ↦ 2 − x`). As três dão a
  **mesma** lógica: o que é verdadeiro está na designação, não no numeral.
* `codB_aritmetica`: em `codB`, a conta é a dos números: `∧ = min`, `∨ = max`, `¬x = 2 − x`, `x → y = min(2, 2 − x + y)`.
* `codC_aritmetica`: em `codC`, invertida: `∧ = max`, `∨ = min`, `x → y = y − x`.
* `codA_quebra_min`: em `codA`, `min` não é `∧` (`min(1, 2) = 1 = T`, mas `T ∧ U = U`).

## O meio
* `meio_tercio_excluido`, `meio_nao_contradicao`: `x ∨ ¬x = T` e `x ∧ ¬x = F` valem **exatamente** fora de `U`.
* `sem_meio_em_Prop`, `rh_nao_e_meio`: nenhuma valoração de `Prop` que respeite `∨`, `¬` e `True` dá `U`; no kernel
  clássico, RH é `0` ou `1`. O "2" de RH é estado de conhecimento, não valor de verdade.
* `luk_aberto_implica_aberto`: em Łukasiewicz, `U → U = T`; em Kleene, `U → U = U`. Łukasiewicz é a que lê um
  condicional provado entre dois enunciados abertos (como `deducao`) como verdadeiro.
* `luk_condicional_aberto`: com hipótese `U`, `U → C = T` força `C ≠ F`: um condicional provado com hipótese aberta
  impede a conclusão de estar refutada (senão, por modus tollens, a hipótese estaria).
* `bochvar_absorve` vs `kleene_nao_absorve`: o `U` de Bochvar (o `𝕀`) contamina tudo; o de Kleene não.
-/

namespace EixoRiemann.Tres

inductive V3
  | F
  | U
  | T
  deriving DecidableEq, Repr, Fintype

open V3

def nao : V3 → V3
  | F => T
  | U => U
  | T => F

def e : V3 → V3 → V3
  | F, _ => F
  | _, F => F
  | T, T => T
  | _, _ => U

def ou : V3 → V3 → V3
  | T, _ => T
  | _, T => T
  | F, F => F
  | _, _ => U

/-- Implicação de Łukasiewicz. -/
def impL : V3 → V3 → V3
  | F, _ => T
  | _, T => T
  | U, U => T
  | U, F => U
  | T, U => U
  | T, F => F

/-- Implicação de Kleene: `¬x ∨ y`. -/
def impK (x y : V3) : V3 := ou (nao x) y

/-- Bochvar: `U` absorvente. -/
def eB (x y : V3) : V3 := if x = U ∨ y = U then U else e x y
def ouB (x y : V3) : V3 := if x = U ∨ y = U then U else ou x y

def posto : V3 → ℕ
  | F => 0
  | U => 1
  | T => 2

/-! ## Codificações -/

def codA : Fin 3 → V3
  | 0 => F
  | 1 => T
  | 2 => U

def codB : Fin 3 → V3
  | 0 => F
  | 1 => U
  | 2 => T

def codC : Fin 3 → V3
  | 0 => T
  | 1 => U
  | 2 => F

theorem codA_bij : Function.Bijective codA := by decide
theorem codB_bij : Function.Bijective codB := by decide
theorem codC_bij : Function.Bijective codC := by decide

/-- `codA` é `codB` com `1` e `2` trocados. -/
theorem codA_eq : ∀ x, codA x = codB (Equiv.swap (1 : Fin 3) 2 x) := by decide

/-- `codC` é `codB` invertida: `x ↦ 2 − x`. -/
theorem codC_eq : ∀ x, codC x = codB (Fin.rev x) := by decide

def impNumB (x y : Fin 3) : Fin 3 := ⟨min 2 (2 - x.val + y.val), by omega⟩
def impNumC (x y : Fin 3) : Fin 3 := ⟨y.val - x.val, by omega⟩

/-- **Em `codB` a lógica é a aritmética**: `∧ = min`, `∨ = max`, `¬x = 2 − x`, `x → y = min(2, 2 − x + y)`. -/
theorem codB_aritmetica :
    (∀ x y, codB (min x y) = e (codB x) (codB y)) ∧ (∀ x y, codB (max x y) = ou (codB x) (codB y)) ∧
      (∀ x, codB (Fin.rev x) = nao (codB x)) ∧ (∀ x y, codB (impNumB x y) = impL (codB x) (codB y)) := by
  decide

/-- **Em `codC` a aritmética inverte**: `∧ = max`, `∨ = min`, `x → y = y − x`. -/
theorem codC_aritmetica :
    (∀ x y, codC (max x y) = e (codC x) (codC y)) ∧ (∀ x y, codC (min x y) = ou (codC x) (codC y)) ∧
      (∀ x, codC (Fin.rev x) = nao (codC x)) ∧ (∀ x y, codC (impNumC x y) = impL (codC x) (codC y)) := by
  decide

/-- **Em `codA`, `min` não é `∧`.** -/
theorem codA_quebra_min : codA (min 1 2) ≠ e (codA 1) (codA 2) := by decide

/-! ## O meio -/

theorem meio_tercio_excluido (x : V3) : ou x (nao x) = T ↔ x ≠ U := by cases x <;> decide

theorem meio_nao_contradicao (x : V3) : e x (nao x) = F ↔ x ≠ U := by cases x <;> decide

/-- **Não há meio em `Prop`**: uma valoração que respeita `∨`, `¬` e `True` nunca dá `U`. -/
theorem sem_meio_em_Prop (v : Prop → V3) (hou : ∀ p q, v (p ∨ q) = ou (v p) (v q))
    (hnao : ∀ p, v (¬ p) = nao (v p)) (hT : v True = T) (p : Prop) : v p ≠ U := by
  rw [← meio_tercio_excluido, ← hnao, ← hou]
  have h : (p ∨ ¬ p) = True := propext (iff_true_intro (Classical.em p))
  rw [h, hT]

open Classical in
/-- A valoração clássica: as hipóteses de `sem_meio_em_Prop` não são vazias. -/
noncomputable def vClass (p : Prop) : V3 := if p then T else F

theorem vClass_ou (p q : Prop) : vClass (p ∨ q) = ou (vClass p) (vClass q) := by
  unfold vClass
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq] <;> rfl

theorem vClass_nao (p : Prop) : vClass (¬ p) = nao (vClass p) := by
  unfold vClass
  by_cases hp : p <;> simp [hp] <;> rfl

theorem vClass_true : vClass True = T := by
  unfold vClass
  simp

/-- **RH não é o meio**: em qualquer valoração que respeite `∨`, `¬` e `True`, RH é `F` ou `T`. -/
theorem rh_nao_e_meio (v : Prop → V3) (hou : ∀ p q, v (p ∨ q) = ou (v p) (v q))
    (hnao : ∀ p, v (¬ p) = nao (v p)) (hT : v True = T) : v RiemannHypothesis ≠ U :=
  sem_meio_em_Prop v hou hnao hT _

theorem luk_aberto_implica_aberto : impL U U = T := rfl

theorem kleene_aberto_implica_aberto : impK U U = U := rfl

theorem luk_modus_ponens : ∀ x y : V3, impL x y = T → x = T → y = T := by decide

/-- `x → y = T` em Łukasiewicz ⟺ `posto x ≤ posto y` (`F < U < T`). -/
theorem impL_T_iff : ∀ x y : V3, impL x y = T ↔ posto x ≤ posto y := by decide

/-- Com hipótese `U`, um condicional verdadeiro impede a conclusão de ser `F`. -/
theorem luk_condicional_aberto : ∀ y : V3, impL U y = T ↔ y ≠ F := by decide

theorem bochvar_absorve : ∀ x : V3, eB U x = U ∧ eB x U = U ∧ ouB U x = U ∧ ouB x U = U := by decide

theorem kleene_nao_absorve : e U F = F ∧ ou U T = T := by decide

end EixoRiemann.Tres

#print axioms EixoRiemann.Tres.codA_eq
#print axioms EixoRiemann.Tres.codC_eq
#print axioms EixoRiemann.Tres.codB_aritmetica
#print axioms EixoRiemann.Tres.codC_aritmetica
#print axioms EixoRiemann.Tres.codA_quebra_min
#print axioms EixoRiemann.Tres.meio_tercio_excluido
#print axioms EixoRiemann.Tres.sem_meio_em_Prop
#print axioms EixoRiemann.Tres.vClass_ou
#print axioms EixoRiemann.Tres.rh_nao_e_meio
#print axioms EixoRiemann.Tres.luk_condicional_aberto
#print axioms EixoRiemann.Tres.impL_T_iff
#print axioms EixoRiemann.Tres.bochvar_absorve
