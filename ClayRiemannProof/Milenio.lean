import ClayRiemannProof.Geometrias
import ClayRiemannProof.Fracoes
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic

/-!
# O padrão dos problemas do milênio: o vizinho falso e o ingrediente que a prova tem de usar

Os sete problemas do milênio têm a mesma forma (README §49): um enunciado "para todo objeto" com um caso baixo
provado, um resultado "quase todo" provado, um limiar crítico (§45) e um **vizinho falso**: um objeto com a mesma
estrutura mole em que o enunciado falha. O vizinho falso diz qual ingrediente a prova tem de usar. Aqui, no kernel,
os dois lados de quatro linhas da comparação:

* **Poincaré** (o único resolvido): `homologia_nao_ve_pi1`. As relações `(st)² = s³ = t⁵` do grupo fundamental da
  esfera de homologia de Poincaré (1904) matam todo grupo abeliano (`abeliano_mata_relacoes`: `H₁ = 0`), mas têm
  solução não comutativa em `SL(2, 𝔽₅)` (`relacoes_SL25`). A homologia não vê `π₁`: o ingrediente é `π₁`.
* **Yang–Mills**: `abeliano_sem_liberdade`, `nao_abeliano_puro`. Com `β₀ = (11/3)C_A − (2/3)n_f`, o grupo abeliano
  (`C_A = 0`, Maxwell/QED) tem `β₀ < 0`; `SU(N)` puro tem `β₀ = 11N/3 > 0`. O ingrediente é o grupo não abeliano.
* **P vs NP**: `existe_funcao_dificil`, `dificil_6_5`, `dificil_10_60`, `poucas_faceis_6_5`. Contagem de Shannon
  (1949): há menos circuitos que funções, logo quase toda função é difícil; nenhuma função explícita foi provada
  difícil (o melhor é `3,1n − o(n)`, Li–Yang 2022). O ingrediente que falta é uma prova sobre uma função
  **explícita**, e as barreiras (relativização, provas naturais, algebrização) dizem quais técnicas não servem.
* **RH, no modelo local**: `Geometrias.petersen_ramanujan` contra `Geometrias.prisma_nao_ramanujan`: as duas zetas
  de Ihara têm equação funcional; só a do grafo de Ramanujan tem a RH. O ingrediente é a positividade local
  `λ² ≤ 4q` (`Nos.no_discriminante`).

`padrao_no_kernel` junta os quatro pares. **O que isto não é**: nenhum dos problemas abertos é resolvido aqui; os
modelos são os vizinhos que a literatura já conhece. `OPEN_MATH = true`.
-/

open Matrix

namespace ClayRiemannProof.Milenio

/-! ## 1. Poincaré: a homologia não vê o grupo fundamental -/

/-- **`H₁ = 0`**: num grupo comutativo, `(st)² = s³ = t⁵` obriga `s = t = 1`. Logo o grupo
`⟨s, t | (st)² = s³ = t⁵⟩` (o `π₁` da esfera de homologia de Poincaré) tem abelianizado trivial. -/
theorem abeliano_mata_relacoes {G : Type*} [CommGroup G] (s t : G) (h1 : (s * t) ^ 2 = s ^ 3)
    (h2 : s ^ 3 = t ^ 5) : s = 1 ∧ t = 1 := by
  have e1 : t ^ 2 = s := by
    have : s ^ 2 * t ^ 2 = s ^ 2 * s := by rw [← mul_pow, h1, pow_succ]
    exact mul_left_cancel this
  have h3 : t ^ 6 = t ^ 5 := by
    rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, e1, h2]
  have e2 : t = 1 := by
    have : t ^ 5 * t = t ^ 5 * 1 := by
      rw [← pow_succ, mul_one, h3]
    exact mul_left_cancel this
  refine ⟨?_, e2⟩
  rw [← e1, e2, one_pow]

/-- `S = [[0, 2], [2, 1]]` em `SL(2, 𝔽₅)`. -/
def S5 : Matrix (Fin 2) (Fin 2) (ZMod 5) := !![0, 2; 2, 1]

/-- `T = [[2, 1], [1, 1]]` em `SL(2, 𝔽₅)`. -/
def T5 : Matrix (Fin 2) (Fin 2) (ZMod 5) := !![2, 1; 1, 1]

/-- **`π₁ ≠ 1`**: `S`, `T` têm determinante 1, satisfazem `(ST)² = S³ = T⁵` (as três valem `−I`), `S ≠ I` e
`ST ≠ TS`. (Verificado pelo kernel com `decide`.) -/
theorem relacoes_SL25 : S5.det = 1 ∧ T5.det = 1 ∧ (S5 * T5) ^ 2 = S5 ^ 3 ∧ S5 ^ 3 = T5 ^ 5 ∧ S5 ≠ 1 ∧
    S5 * T5 ≠ T5 * S5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [S5, Matrix.det_fin_two_of]; decide
  · rw [T5, Matrix.det_fin_two_of]; decide
  all_goals decide

/-- **O vizinho falso de Poincaré (1904)**: as relações do `π₁` da esfera de homologia dão `H₁ = 0` (todo quociente
abeliano é trivial), e mesmo assim têm solução não trivial e não comutativa. "Homologia de `S³`" não basta; o
enunciado certo (e o que Perelman provou) pede `π₁ = 1`. -/
theorem homologia_nao_ve_pi1 :
    (∀ (G : Type) [CommGroup G] (s t : G), (s * t) ^ 2 = s ^ 3 → s ^ 3 = t ^ 5 → s = 1 ∧ t = 1) ∧
      ∃ S T : Matrix (Fin 2) (Fin 2) (ZMod 5), S.det = 1 ∧ T.det = 1 ∧ (S * T) ^ 2 = S ^ 3 ∧ S ^ 3 = T ^ 5 ∧
        S ≠ 1 ∧ S * T ≠ T * S :=
  ⟨fun _ _ s t h1 h2 => abeliano_mata_relacoes s t h1 h2, S5, T5, relacoes_SL25⟩

/-! ## 2. Yang–Mills: o abeliano não é assintoticamente livre -/

/-- `β₀ = (11/3)·C_A − (2/3)·n_f` (Casimir adjunto `C_A`; `n_f` férmions de Dirac na fundamental). -/
def beta0Gauge (CA nf : ℚ) : ℚ := 11 * CA / 3 - 2 * nf / 3

/-- Para `SU(N)`, `C_A = N`: é o `β₀` de `Fracoes`. -/
theorem beta0Gauge_SU (N nf : ℚ) : beta0Gauge N nf = Fracoes.beta0 N nf := rfl

/-- **Abeliano (`C_A = 0`, Maxwell/QED) com matéria carregada: `β₀ < 0`**, sem liberdade assintótica. -/
theorem abeliano_sem_liberdade {nf : ℚ} (h : 0 < nf) : beta0Gauge 0 nf < 0 := by
  unfold beta0Gauge
  linarith

/-- **Não abeliano puro (`SU(N)`, `N ≥ 2`, sem férmions): `β₀ = 11N/3 > 0`.** -/
theorem nao_abeliano_puro {N : ℚ} (h : 2 ≤ N) : 0 < beta0Gauge N 0 ∧ beta0Gauge N 0 = 11 * N / 3 := by
  unfold beta0Gauge
  constructor <;> [linarith; ring]

/-! ## 3. P vs NP: quase toda função é difícil (Shannon), nenhuma explícita provada -/

/-- Um circuito com `s` portas sobre `n` entradas: cada porta escolhe uma das 16 funções booleanas de dois bits
(base `B₂`) e dois fios entre os `n + s`. -/
abbrev Circuito (n s : ℕ) := (Fin s → Fin 16) × (Fin s → Fin (n + s)) × (Fin s → Fin (n + s))

/-- A porta `op` aplicada a `(x, y)`: o bit `2x + y` da tabela-verdade `op`. -/
def porta (op : Fin 16) (x y : Bool) : Bool := op.val.testBit (2 * x.toNat + y.toNat)

/-- Os valores dos fios depois de `i` portas (fio ainda não calculado vale `false`). -/
def fios {n s : ℕ} (c : Circuito n s) (x : Fin n → Bool) : ℕ → ℕ → Bool
  | 0 => fun j => if h : j < n then x ⟨j, h⟩ else false
  | i + 1 => fun j =>
    if h : i < s then
      (if j = n + i then porta (c.1 ⟨i, h⟩) (fios c x i (c.2.1 ⟨i, h⟩)) (fios c x i (c.2.2 ⟨i, h⟩))
       else fios c x i j)
    else fios c x i j

/-- A função calculada: o último fio. -/
def funcao {n s : ℕ} (c : Circuito n s) : (Fin n → Bool) → Bool := fun x => fios c x s (n + s - 1)

theorem card_circuito (n s : ℕ) : Fintype.card (Circuito n s) = 16 ^ s * (n + s) ^ s * (n + s) ^ s := by
  simp [Circuito, Fintype.card_prod, mul_assoc]

/-- **Contagem de Shannon**: se há menos circuitos com `s` portas que funções de `n` bits
(`16ˢ(n + s)²ˢ < 2^(2ⁿ)`), alguma função não é calculada por nenhum deles. -/
theorem existe_funcao_dificil {n s : ℕ} (h : 16 ^ s * (n + s) ^ s * (n + s) ^ s < 2 ^ (2 ^ n)) :
    ∃ f : (Fin n → Bool) → Bool, ∀ c : Circuito n s, funcao c ≠ f := by
  by_contra hc
  push Not at hc
  have hs : Function.Surjective (funcao : Circuito n s → (Fin n → Bool) → Bool) := fun f => hc f
  have := Fintype.card_le_of_surjective _ hs
  rw [card_circuito] at this
  simp at this
  omega

/-- Há função de 6 bits que nenhum circuito de 5 portas calcula. -/
theorem dificil_6_5 : ∃ f : (Fin 6 → Bool) → Bool, ∀ c : Circuito 6 5, funcao c ≠ f :=
  existe_funcao_dificil (by norm_num)

set_option exponentiation.threshold 2000 in
/-- Há função de 10 bits que nenhum circuito de 60 portas calcula (`16⁶⁰·70¹²⁰ < 2¹⁰²⁴`). -/
theorem dificil_10_60 : ∃ f : (Fin 10 → Bool) → Bool, ∀ c : Circuito 10 60, funcao c ≠ f :=
  existe_funcao_dificil (by norm_num)

/-- **Poucas são fáceis**: os circuitos de 5 portas sobre 6 bits são menos de `1/600` das `2⁶⁴` funções. -/
theorem poucas_faceis_6_5 : Fintype.card (Circuito 6 5) * 600 < 2 ^ (2 ^ 6) := by
  rw [card_circuito]
  norm_num

/-! ## 4. Os quatro pares no kernel -/

/-- **O padrão no kernel**: em cada linha, o lado com o ingrediente e o vizinho sem ele.

* RH local: Petersen (Ramanujan, RH de Ihara) e o prisma `K₇ □ K₂` (não Ramanujan, zeros fora);
* Poincaré: `H₁ = 0` sem `π₁ = 1`;
* Yang–Mills: não abeliano `β₀ > 0`, abeliano `β₀ < 0`;
* P vs NP: existe função de 10 bits que pede mais de 60 portas, sem que se saiba qual. -/
theorem padrao_no_kernel :
    (Geometrias.Ramanujan Geometrias.petersen 2 ∧ ¬ Geometrias.Ramanujan Geometrias.prisma 6) ∧
      ((∀ (G : Type) [CommGroup G] (s t : G), (s * t) ^ 2 = s ^ 3 → s ^ 3 = t ^ 5 → s = 1 ∧ t = 1) ∧
        ∃ S T : Matrix (Fin 2) (Fin 2) (ZMod 5), S.det = 1 ∧ T.det = 1 ∧ (S * T) ^ 2 = S ^ 3 ∧ S ^ 3 = T ^ 5 ∧
          S ≠ 1 ∧ S * T ≠ T * S) ∧
      (0 < beta0Gauge 3 0 ∧ beta0Gauge 0 1 < 0) ∧
      (∃ f : (Fin 10 → Bool) → Bool, ∀ c : Circuito 10 60, funcao c ≠ f) :=
  ⟨⟨Geometrias.petersen_ramanujan, Geometrias.prisma_nao_ramanujan⟩, homologia_nao_ve_pi1,
    ⟨(nao_abeliano_puro (by norm_num)).1, abeliano_sem_liberdade (by norm_num)⟩, dificil_10_60⟩

end ClayRiemannProof.Milenio
