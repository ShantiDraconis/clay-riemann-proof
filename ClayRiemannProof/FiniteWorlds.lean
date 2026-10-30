import ClayRiemannProof.Main
import ClayRiemannProof.Zeta.Symmetry

/-!
# A ponte entre o enunciado do Clay e as aritméticas finitas

Uma aritmética finita com **último inteiro** `Z` existe sem contradição: `{0, …, Z}` com a soma
saturada `a ⊕ b = min Z (a + b)`, em que `Z ⊕ 1 = Z`. O preço é o cancelamento (`cancelamento_falha`).
Já um último inteiro dentro de `ℕ` é contraditório (`nao_ha_ultimo_inteiro`).

Cada mundo finito vê só os zeros de altura `|Im s| ≤ Z`. Neste arquivo:

* `RHateZ Z`: todo zero não trivial com `|Im s| ≤ Z` está na reta `Re s = 1/2` (uma afirmação finita);
* `RHnoMundo Z`: a mesma afirmação lida dentro da aritmética finita `Sat Z`, para todo elemento dela;
* **`target_iff_todos_os_mundos`**: o enunciado do Clay ⟺ RH vale em **todo** mundo finito;
* **`not_target_iff_um_mundo`**: RH falsa ⟺ existe **um** mundo finito onde ela falha (um contraexemplo,
  se existir, mora numa altura finita);
* `rhNoMundo_zero`: o mundo `Z = 0` está certificado (não há zero não trivial real);
* `PlattTrudgian2021` e `rhNoMundo_platt_trudgian`: o mundo `Z = 3 000 175 332 800`, condicional à verificação
  publicada (hipótese nomeada, nunca `axiom`).

**O que isto não é**: nenhum mundo finito isolado implica o enunciado do Clay. A passagem de "cada `Z`" para
"todo `Z`" é exatamente o problema em aberto. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.FiniteWorlds

open ClayRiemannProof.Zeta.Symmetry

/-! ## 1. A aritmética finita com último inteiro -/

/-- `{0, …, Z}`. -/
abbrev Sat (Z : ℕ) := Fin (Z + 1)

/-- Soma saturada: `a ⊕ b = min Z (a + b)`. -/
def satAdd {Z : ℕ} (a b : Sat Z) : Sat Z := ⟨min Z (a.val + b.val), by omega⟩

/-- Todo elemento de `Sat Z` é no máximo `Z`: `Z` é o último inteiro deste mundo. -/
theorem le_ultimo {Z : ℕ} (a : Sat Z) : a.val ≤ Z := Nat.lt_succ_iff.mp a.isLt

/-- O último inteiro absorve: `Z ⊕ a = Z`. -/
theorem ultimo_absorve {Z : ℕ} (a : Sat Z) : satAdd (Fin.last Z) a = Fin.last Z := by
  ext; simp [satAdd]

theorem satAdd_comm {Z : ℕ} (a b : Sat Z) : satAdd a b = satAdd b a := by
  ext; simp [satAdd, Nat.add_comm]

theorem satAdd_assoc {Z : ℕ} (a b c : Sat Z) : satAdd (satAdd a b) c = satAdd a (satAdd b c) := by
  ext; simp only [satAdd]; omega

/-- O preço do último inteiro: o cancelamento falha (`0 ⊕ Z = 1 ⊕ Z` com `0 ≠ 1`). -/
theorem cancelamento_falha {Z : ℕ} (hZ : 1 ≤ Z) :
    ∃ a b c : Sat Z, satAdd a c = satAdd b c ∧ a ≠ b := by
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, Fin.last Z, ?_, ?_⟩
  · ext; simp [satAdd]
  · intro h; have := congrArg Fin.val h; simp at this

/-- Em `ℕ` não há último inteiro: para todo `Z`, `Z + 1` é maior. -/
theorem nao_ha_ultimo_inteiro : ¬ ∃ Z : ℕ, ∀ n : ℕ, n ≤ Z := by
  rintro ⟨Z, h⟩
  have := h (Z + 1)
  omega

/-! ## 2. RH em cada mundo finito -/

/-- **RH até a altura `Z`**: todo zero não trivial com `|Im s| ≤ Z` está na reta crítica. -/
def RHateZ (Z : ℕ) : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬ ∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → |s.im| ≤ Z →
    s.re = 1 / 2

/-- **RH no mundo finito `Sat Z`**: para cada inteiro `h` desse mundo, RH até a altura `h`. -/
def RHnoMundo (Z : ℕ) : Prop := ∀ h : Sat Z, RHateZ h.val

/-- Mundos maiores contêm os menores. -/
theorem RHateZ_anti {Z Z' : ℕ} (hZZ : Z ≤ Z') (h : RHateZ Z') : RHateZ Z :=
  fun s hz ht hs1 him => h s hz ht hs1 (him.trans (by exact_mod_cast hZZ))

/-- Dentro do mundo `Sat Z`, RH equivale a RH até o último inteiro `Z`. -/
theorem rhNoMundo_iff (Z : ℕ) : RHnoMundo Z ↔ RHateZ Z :=
  ⟨fun h => by simpa using h (Fin.last Z), fun h a => RHateZ_anti (le_ultimo a) h⟩

/-! ## 3. A ponte -/

/-- **A ponte**: o enunciado do Clay ⟺ RH vale em **todo** mundo finito `Sat Z`. -/
theorem target_iff_todos_os_mundos : Target ↔ ∀ Z : ℕ, RHnoMundo Z := by
  constructor
  · intro h Z
    exact (rhNoMundo_iff Z).2 fun s hz ht hs1 _ => h s hz ht hs1
  · intro h s hz ht hs1
    obtain ⟨Z, hZ⟩ := exists_nat_ge |s.im|
    exact (rhNoMundo_iff Z).1 (h Z) s hz ht hs1 hZ

/-- **RH falsa ⟺ existe um mundo finito onde ela falha**: um contraexemplo, se existir, tem altura finita. -/
theorem not_target_iff_um_mundo : ¬ Target ↔ ∃ Z : ℕ, ¬ RHnoMundo Z := by
  rw [target_iff_todos_os_mundos, not_forall]

/-! ## 4. Mundos certificados -/

/-- **O mundo `Z = 0` está certificado**: não existe zero não trivial real. -/
theorem rhNoMundo_zero : RHnoMundo 0 := by
  rw [rhNoMundo_iff]
  intro s hz ht hs1 him
  have him0 : s.im = 0 := abs_nonpos_iff.mp (by simpa using him)
  exfalso
  by_cases hle : s.re ≤ 0
  · exact ht (zero_trivial_de_re_nao_pos hz hle)
  by_cases hge : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hge hz
  exact im_ne_zero_of_mem_Z ⟨hz, by linarith, by linarith⟩ him0

/-- **Resultado externo publicado**: D. Platt e T. Trudgian, *The Riemann hypothesis is true up to
`3·10¹²`*, Bull. London Math. Soc. 53 (2021) 792–797: todos os zeros não triviais com
`0 < Im s ≤ 3 000 175 332 800` estão na reta crítica. Pela conjugação (`espelho_mem_Z`) e por
`rhNoMundo_zero`, isso dá a forma abaixo com `|Im s|`. Hipótese nomeada; **não** é provado aqui. -/
def PlattTrudgian2021 : Prop := RHateZ 3000175332800

/-- O mundo `Z = 3 000 175 332 800`, condicional à verificação publicada. -/
theorem rhNoMundo_platt_trudgian (h : PlattTrudgian2021) : RHnoMundo 3000175332800 :=
  (rhNoMundo_iff _).2 h

end ClayRiemannProof.FiniteWorlds
