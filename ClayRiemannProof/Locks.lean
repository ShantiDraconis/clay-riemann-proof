import ClayRiemannProof.Main
import ClayRiemannProof.Zeta.Symmetry

/-!
# As "travas" de Euler: o que é teorema e o que não é

A conversa propôs duas "travas" que segurariam os zeros na reta crítica. Este arquivo separa, no kernel, o que
nelas é verdadeiro do que não decorre delas.

* **`target_iff_desvio_zero`**: o enunciado do Clay ⟺ o desvio `b = Re ρ − ½` é zero para todo zero não trivial.
  É a forma exata de "o segundo universo colapsa": uma reformulação, não uma prova.
* **Trava 1** (`trava1_algebra`): para `p > 1`, `p^{−σ} = p^{−(1−σ)} ⟺ σ = ½`. É verdade como álgebra, mas **não
  restringe os zeros**: a equação funcional vale em **todo** `σ`, inclusive `0,7`
  (`ponte_vale_em_todo_sigma`, `ponte_em_sete_decimos`); não há ponte que "quebra" fora da reta.
* **Simetria não basta** (`simetria_nao_basta`): `G(s) = (s − ¼)(s − ¾)` satisfaz `G(1 − s) = G(s)` e tem zeros em
  `¼` e `¾`.
* **Trava 2** (`trava2_complexo`): em `ℂ`, `(1 + i)(1 − i) = 2 ≠ 0`, e `ℂ` não tem divisores de zero. Isso **não**
  impede zeros: `ζ(−2) = 0` em `ℂ` mesmo (`zeta_tem_zeros_em_C`). (Ver também `ClayRiemannProof.Bicomplex`: o
  segundo universo `j` não cria nem esconde zeros.)
* **A trava real do produto de Euler** (`euler_trava`): `ζ(s) ≠ 0` para `Re s ≥ 1`. Ela vale onde o produto converge
  e na sua borda; dentro da faixa crítica o produto não converge, e o que ele impõe ali é o problema em aberto.

Nada aqui prova RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Locks

open Complex

/-- **`b = 0`**: o enunciado do Clay ⟺ todo zero não trivial tem desvio `Re ρ − ½` nulo. -/
theorem target_iff_desvio_zero :
    Target ↔ ∀ ρ : ℂ, riemannZeta ρ = 0 → (¬ ∃ n : ℕ, ρ = -2 * (n + 1)) → ρ ≠ 1 → ρ.re - 1 / 2 = 0 :=
  ⟨fun h ρ hz ht h1 => by rw [h ρ hz ht h1]; ring,
   fun h ρ hz ht h1 => by linarith [h ρ hz ht h1]⟩

/-- **Trava 1, como álgebra**: para `p > 1`, `p^{−σ} = p^{−(1−σ)} ⟺ σ = ½`. -/
theorem trava1_algebra {p σ : ℝ} (hp : 1 < p) : p ^ (-σ) = p ^ (-(1 - σ)) ↔ σ = 1 / 2 := by
  rw [Real.rpow_right_inj (by linarith) (by linarith)]
  constructor <;> intro h <;> linarith

/-- **A ponte `s ↔ 1 − s` vale em todo `σ`**: `Λ(1 − s) = Λ(s)` para todo `s` (equação funcional da Mathlib). -/
theorem ponte_vale_em_todo_sigma (s : ℂ) : completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

/-- Em particular em `σ = 0,7`: `Λ(0,3 − it) = Λ(0,7 + it)` para todo `t`. A "ponte" não quebra fora da reta. -/
theorem ponte_em_sete_decimos (t : ℝ) :
    completedRiemannZeta ((3 / 10 : ℂ) - t * I) = completedRiemannZeta ((7 / 10 : ℂ) + t * I) := by
  rw [← ponte_vale_em_todo_sigma]
  congr 1
  ring

/-- **A simetria sozinha não segura os zeros na reta**. -/
theorem simetria_nao_basta :
    ∃ G : ℂ → ℂ, (∀ s, G (1 - s) = G s) ∧ G (1 / 4) = 0 ∧ G (3 / 4) = 0 ∧ (1 / 4 : ℂ).re ≠ 1 / 2 := by
  refine ⟨fun s => (s - 1 / 4) * (s - 3 / 4), fun s => by ring, by ring, by ring, ?_⟩
  norm_num

/-- **Trava 2 em `ℂ`**: `(1 + i)(1 − i) = 2`. -/
theorem trava2_complexo : (1 + I) * (1 - I) = 2 := by
  ring_nf; rw [I_sq]; ring

/-- `ℂ` não tem divisores de zero... -/
theorem sem_divisor_de_zero (a b : ℂ) : a * b = 0 ↔ a = 0 ∨ b = 0 := mul_eq_zero

/-- ... e mesmo assim `ζ` se anula em `ℂ`: não ter divisores de zero não impede zeros. -/
theorem zeta_tem_zeros_em_C : riemannZeta (-2) = 0 := by
  simpa using riemannZeta_neg_two_mul_nat_add_one 0

/-- **A trava real do produto de Euler**: `ζ(s) ≠ 0` para `Re s ≥ 1` (Hadamard e de la Vallée Poussin na borda). -/
theorem euler_trava {s : ℂ} (h : 1 ≤ s.re) : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re h

/-- **O retângulo**: um zero na faixa vem com `1 − ρ̄` (mesma altura, espelhado em `½`) e com `ρ̄`. -/
theorem retangulo {ρ : ℂ} (hρ : ρ ∈ ClayRiemannProof.Zeta.Symmetry.Z) :
    ClayRiemannProof.Zeta.Symmetry.torcao ρ ∈ ClayRiemannProof.Zeta.Symmetry.Z ∧
      ClayRiemannProof.Zeta.Symmetry.espelho ρ ∈ ClayRiemannProof.Zeta.Symmetry.Z :=
  ⟨ClayRiemannProof.Zeta.Symmetry.torcao_mem_Z hρ, ClayRiemannProof.Zeta.Symmetry.espelho_mem_Z hρ⟩

end ClayRiemannProof.Locks
