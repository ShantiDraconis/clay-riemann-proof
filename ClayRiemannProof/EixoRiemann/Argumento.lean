import ClayRiemannProof.EixoRiemann.Reformulacao
import ClayRiemannProof.Paridade
import ClayRiemannProof.WeilRota
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# O argumento no eixo Riemann: leis, operadores, pontes, habitantes e inabitantes

Cada rota de fechamento proposta vira aqui um enunciado no kernel, com o seu estatuto exato.

## Álgebra
* `idempotente_complexo`, `Idem.idempotentes`: `ℂ` tem 2 idempotentes; `Idem` tem exatamente 4: `0, 1, e, 1 − e`.
* `colapso`: autovalor de projeção é `0` ou `1` (álgebra linear, incondicional).
* `autovalor_colapsa`: `1/(1 + 4δ²) ∈ {0, 1} ⟹ δ = 0`.

## Pontes condicionais (rotas de fechamento)
* `projecao_iff_rh`: **a "projeção do espelho" é RH**. Existir um operador idempotente com autovalor
  `1/(1 + 4δ²)` em cada zero ⟺ RH. O colapso é trivial; toda a dificuldade está em construir o operador a partir
  de `ζ` e dos primos sem usar os zeros, e isso ninguém sabe fazer.
* `rhIdem_iff_weil`: com o critério de Weil (`ProgramaDeWeil`, hipótese nomeada), RH no eixo ⟺ positividade.
* `somaDeQuadrados_iff`: "`S(φ) = c²`" ⟺ RH. A soma de quadrados real é grátis quando há positividade
  (`c = √S`); o conteúdo teria de estar em **construir** `c` a partir dos primos.
* `ponte_horizontal_dlvp`: com a região de de la Vallée Poussin (teorema de 1899, ainda fora da Mathlib, aqui
  hipótese nomeada), uma ponte horizontal na altura `t` tem `|δ| < 1 − 2c/log t`. A região afasta a ponte da
  **borda**; não aproxima `δ` de `0`.

## Pontes incondicionais
* `ponte_horizontal_curta`: toda ponte horizontal na faixa tem `|δ| < 1`.
* `tres_quatro_um`, `positividade_aritmetica`: `3 + 4 cos θ + cos 2θ ≥ 0` e `Λ(n)·n^{−σ}·(3 + 4 cos + cos 2) ≥ 0`,
  o motor das regiões livres de zeros (Mathlib já tira daí `ζ ≠ 0` em `Re s ≥ 1`).

## Topologia
* `torcao_isometria`, `torcao_troca_lados`: a torção é isometria, fixa só a reta e troca os dois lados; uma ponte
  horizontal atravessa a reta.
* `pontes_horizontais_finitas_e_pares`: numa janela de altura, as pontes horizontais (= zeros fora da reta) são
  em número finito e par.

## Habitantes e inabitantes
* habitado: `habitante_ponte_nao_trivial` (`−2 → −4`, `δ = −2`).
* inabitados: `inabitante_ponta_na_borda`, `inabitante_quarteto_conectado`, `inabitante_meio_da_ponte`.
* em aberto: `PonteHorizontal`. Habitado ⟺ RH falsa.
-/

open ClayRiemannProof.Zeta.Symmetry

namespace EixoRiemann

/-! ## Álgebra -/

theorem idempotente_complexo {c : ℂ} (h : c * c = c) : c = 0 ∨ c = 1 := by
  have h2 : c * (c - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact Or.inl h3
  · exact Or.inr (sub_eq_zero.mp h3)

/-- `Idem` tem exatamente 4 idempotentes: `0`, `1`, `e` e `1 − e`. -/
theorem Idem.idempotentes (x : Idem) :
    x * x = x ↔ x = ⟨0, 0⟩ ∨ x = ⟨1, 0⟩ ∨ x = ⟨0, 1⟩ ∨ x = ⟨1, -1⟩ := by
  constructor
  · intro h
    have hz : x.z * x.z = x.z := by
      have := congrArg Idem.z h
      simpa using this
    have hw : (x.z + x.w) * (x.z + x.w) = x.z + x.w := by
      have := congrArg Idem.w h
      simp only [Idem.mul_w] at this
      linear_combination this + hz
    rcases idempotente_complexo hz with a | a <;> rcases idempotente_complexo hw with b | b
    · exact Or.inl (Idem.ext a (show x.w = 0 by linear_combination b - a))
    · exact Or.inr (Or.inr (Or.inl (Idem.ext a (show x.w = 1 by linear_combination b - a))))
    · exact Or.inr (Or.inr (Or.inr (Idem.ext a (show x.w = -1 by linear_combination b - a))))
    · exact Or.inr (Or.inl (Idem.ext a (show x.w = 0 by linear_combination b - a)))
  · rintro (rfl | rfl | rfl | rfl) <;> ext <;> norm_num [Idem.mul_z, Idem.mul_w]

/-- **Colapso**: um autovalor de projeção é `0` ou `1`. -/
theorem colapso {V : Type*} [AddCommGroup V] [Module ℂ V] (P : V →ₗ[ℂ] V) (hP : P ∘ₗ P = P)
    {v : V} (hv : v ≠ 0) {c : ℂ} (h : P v = c • v) : c = 0 ∨ c = 1 := by
  apply idempotente_complexo
  have h1 : P (P v) = P v := by rw [← LinearMap.comp_apply, hP]
  rw [h, map_smul, h, smul_smul] at h1
  have h2 : (c * c - c) • v = 0 := by rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 hv

/-- O autovalor proposto para a ponte em `ρ = 1/2 + δ + iγ`. -/
noncomputable def autovalor (δ : ℝ) : ℂ := ((1 / (1 + 4 * δ ^ 2) : ℝ) : ℂ)

theorem autovalor_colapsa {δ : ℝ} (h : autovalor δ = 0 ∨ autovalor δ = 1) : δ = 0 := by
  have hpos : 0 < 1 + 4 * δ ^ 2 := by positivity
  unfold autovalor at h
  rcases h with h | h
  · have h0 : (1 / (1 + 4 * δ ^ 2) : ℝ) = 0 := by exact_mod_cast h
    have h1 : 0 < (1 / (1 + 4 * δ ^ 2) : ℝ) := by positivity
    linarith
  · have h1 : (1 / (1 + 4 * δ ^ 2) : ℝ) = 1 := by exact_mod_cast h
    rw [div_eq_one_iff_eq hpos.ne'] at h1
    have h2 : δ ^ 2 = 0 := by linarith
    exact (pow_eq_zero_iff two_ne_zero).mp h2

/-! ## Pontes condicionais -/

/-- A "projeção do espelho": um operador idempotente com um autovetor de autovalor `1/(1 + 4δ²)` em cada zero. -/
structure Espelho where
  V : Type
  [grupo : AddCommGroup V]
  [modulo : Module ℂ V]
  P : V →ₗ[ℂ] V
  idem : P ∘ₗ P = P
  autovetor : ∀ ρ ∈ Z, ∃ v : V, v ≠ 0 ∧ P v = autovalor (ρ.re - 1 / 2) • v

attribute [instance] Espelho.grupo Espelho.modulo

/-- **A projeção do espelho é RH.** -/
theorem projecao_iff_rh : Nonempty Espelho ↔ RHFaixa := by
  constructor
  · rintro ⟨E⟩ ρ hρ
    obtain ⟨v, hv, hPv⟩ := E.autovetor ρ hρ
    have := autovalor_colapsa (colapso E.P E.idem hv hPv)
    linarith
  · intro h
    refine ⟨{ V := ℂ, P := LinearMap.id, idem := LinearMap.id_comp _, autovetor := ?_ }⟩
    intro ρ hρ
    refine ⟨1, one_ne_zero, ?_⟩
    rw [h ρ hρ, sub_self]
    simp [autovalor]

open ClayRiemannProof.WeilRota in
/-- Com o critério de Weil como hipótese nomeada: RH no eixo ⟺ positividade de Weil em toda escala. -/
theorem rhIdem_iff_weil {F : Type*} (P : ProgramaDeWeil F) :
    RHIdem ↔ ∀ L : ℝ, 0 < L → ∀ g ∈ P.teste L, 0 ≤ P.W g :=
  rh_iff_rhIdem.symm.trans P.criterio

open ClayRiemannProof.WeilRota in
/-- **Soma de quadrados ⟺ RH**: a representação `S(φ) = c²` existe exatamente quando há positividade. -/
theorem somaDeQuadrados_iff {F : Type*} (P : ProgramaDeWeil F) :
    (∀ L : ℝ, 0 < L → ∀ g ∈ P.teste L, ∃ c : ℝ, P.W g = c ^ 2) ↔ RHIdem := by
  rw [rhIdem_iff_weil P]
  constructor
  · intro h L hL g hg
    obtain ⟨c, hc⟩ := h L hL g hg
    rw [hc]
    exact sq_nonneg c
  · intro h L hL g hg
    exact ⟨Real.sqrt (P.W g), (Real.sq_sqrt (h L hL g hg)).symm⟩

/-- Região de de la Vallée Poussin (1899) com constante `c`, como hipótese nomeada. -/
def RegiaoDLVP (c : ℝ) : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → 3 ≤ |s.im| → s.re < 1 - c / Real.log |s.im|

/-- **dLVP em pontes**: uma ponte horizontal na altura `t ≥ 3` tem `|δ| < 1 − 2c/log t`. Afasta da borda; não fecha. -/
theorem ponte_horizontal_dlvp {c : ℝ} (hR : RegiaoDLVP c) {s : ℂ} {r : ℝ} (hs : s ∈ Z)
    (hsr : s + (r : ℂ) ∈ Z) (ht : 3 ≤ |s.im|) : |r| < 1 - 2 * (c / Real.log |s.im|) := by
  have him : (s + (r : ℂ)).im = s.im := by simp
  obtain ⟨z3, -, -⟩ := torcao_mem_Z hs
  obtain ⟨z4, -, -⟩ := torcao_mem_Z hsr
  obtain ⟨z1, -, -⟩ := hs
  obtain ⟨z2, -, -⟩ := hsr
  have a := hR s z1 ht
  have b := hR _ z2 (by rw [him]; exact ht)
  have a' := hR _ z3 (by rw [im_tor]; exact ht)
  have b' := hR _ z4 (by rw [im_tor, him]; exact ht)
  rw [him] at b
  rw [im_tor, re_torcao] at a'
  rw [im_tor, him, re_torcao] at b'
  rw [Complex.add_re, Complex.ofReal_re] at b b'
  rw [abs_lt]
  constructor <;> linarith

/-! ## Pontes incondicionais -/

/-- Toda ponte horizontal na faixa tem `|δ| < 1`. -/
theorem ponte_horizontal_curta {s : ℂ} {r : ℝ} (hs : s ∈ Z) (hsr : s + (r : ℂ) ∈ Z) : |r| < 1 := by
  obtain ⟨-, a0, a1⟩ := hs
  obtain ⟨-, b0, b1⟩ := hsr
  rw [Complex.add_re, Complex.ofReal_re] at b0 b1
  rw [abs_lt]
  constructor <;> linarith

/-- A desigualdade 3-4-1: `3 + 4 cos θ + cos 2θ = 2(1 + cos θ)² ≥ 0`. -/
theorem tres_quatro_um (θ : ℝ) : 0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [Real.cos_two_mul]
  nlinarith [sq_nonneg (1 + Real.cos θ)]

/-- **Positividade aritmética**: cada termo `Λ(n)·n^{−σ}·(3 + 4 cos(t log n) + cos(2t log n))` é `≥ 0`. -/
theorem positividade_aritmetica (n : ℕ) (σ t : ℝ) :
    0 ≤ ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) *
      (3 + 4 * Real.cos (t * Real.log n) + Real.cos (2 * (t * Real.log n))) :=
  mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (tres_quatro_um _)

/-! ## Topologia -/

theorem torcao_isometria (a b : ℂ) : dist (torcao a) (torcao b) = dist a b := by
  unfold torcao
  rw [Complex.dist_eq, Complex.dist_eq, sub_sub_sub_cancel_left, ← map_sub (starRingEnd ℂ), Complex.norm_conj, norm_sub_rev]

/-- Fora da reta, `ρ` e `1 − ρ̄` estão em lados opostos: a ponte horizontal atravessa a reta. -/
theorem torcao_troca_lados {ρ : ℂ} (h : ρ.re ≠ 1 / 2) : (ρ.re - 1 / 2) * ((torcao ρ).re - 1 / 2) < 0 := by
  rw [re_torcao]
  have h0 : ρ.re - 1 / 2 ≠ 0 := sub_ne_zero.mpr h
  have : 0 < (ρ.re - 1 / 2) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h0))
  nlinarith

/-- Numa janela `T₁ < Im ≤ T₂` (`T₁ ≥ 1`), as pontes horizontais (uma por zero fora da reta) são finitas e pares. -/
theorem pontes_horizontais_finitas_e_pares {T₁ T₂ : ℝ} (h : 1 ≤ T₁) :
    (ClayRiemannProof.Paridade.Fora T₁ T₂).Finite ∧ Even (ClayRiemannProof.Paridade.Fora T₁ T₂).ncard :=
  ⟨ClayRiemannProof.Paridade.fora_finito h, ClayRiemannProof.Paridade.fora_par h⟩

/-! ## Habitantes e inabitantes -/

theorem habitante_ponte_nao_trivial : ∃ x : Idem, x.w ≠ 0 ∧ Idem.aplica riemannZeta x = ⟨0, 0⟩ :=
  ⟨⟨-2, -2⟩, by norm_num, Idem.trivial_carrega_trivial⟩

theorem inabitante_ponta_na_borda : ¬ ∃ x : Idem, Idem.aplica riemannZeta x = ⟨0, 0⟩ ∧ 1 ≤ x.z.re := by
  rintro ⟨x, hx, h1⟩
  rw [Idem.aplica_eq_zero] at hx
  exact riemannZeta_ne_zero_of_one_le_re h1 hx.1

theorem inabitante_quarteto_conectado :
    ¬ ∃ s t : ℂ, orbita s ≠ orbita t ∧ ¬ Disjoint (orbita s) (orbita t) := by
  rintro ⟨s, t, hne, hnd⟩
  rcases orbitas_iguais_ou_disjuntas s t with h | h
  · exact hne h
  · exact hnd h

theorem inabitante_meio_da_ponte :
    ¬ ∀ x y : Idem, Idem.avalia (1 / 2) (x * y) = Idem.avalia (1 / 2) x * Idem.avalia (1 / 2) y := by
  intro h
  rcases (Idem.avalia_mul_iff (1 / 2)).mp h with h' | h' <;> norm_num at h'

/-! ## O esqueleto com `sorry`: pontes sem amarra com ζ -/

/-- Uma "ponte" só como par `(δ, γ)`, sem exigir que seja zero de ζ. -/
structure PonteLivre where
  δ : ℝ
  γ : ℝ

/-- **Os dois lemas do esqueleto, sobre pontes sem amarra com ζ, são contraditórios**: a ponte livre `δ = 1/4`
teria autovalor `4/5` numa projeção. Eles não são "difíceis": são falsos. A versão correta quantifica só sobre
`ρ ∈ Z` (`Espelho.autovetor`), e aí é equivalente a RH (`projecao_iff_rh`). -/
theorem esqueleto_sem_amarra_inconsistente {V : Type*} [AddCommGroup V] [Module ℂ V]
    (P : V →ₗ[ℂ] V) (v : PonteLivre → V) (hP : P ∘ₗ P = P) (hv : ∀ ρ, v ρ ≠ 0)
    (hλ : ∀ ρ, P (v ρ) = autovalor ρ.δ • v ρ) : False := by
  have h := autovalor_colapsa (colapso P hP (hv ⟨1 / 4, 0⟩) (hλ ⟨1 / 4, 0⟩))
  norm_num at h

/-- Para **qualquer** projeção (em particular a projeção ortogonal no span de `p^{−it}`, feita só com primos),
nenhum vetor não nulo tem autovalor `1/(1 + 4δ²)` com `δ ≠ 0`. Construir `P` com primos torna a idempotência
grátis e o lema do autovalor equivalente a "não existe zero fora da reta". -/
theorem projecao_sem_autovalor_intermediario {V : Type*} [AddCommGroup V] [Module ℂ V]
    (P : V →ₗ[ℂ] V) (hP : P ∘ₗ P = P) {v : V} (hv : v ≠ 0) {δ : ℝ} (hδ : δ ≠ 0) :
    P v ≠ autovalor δ • v := fun h => hδ (autovalor_colapsa (colapso P hP hv h))

end EixoRiemann

#print axioms EixoRiemann.Idem.idempotentes
#print axioms EixoRiemann.colapso
#print axioms EixoRiemann.autovalor_colapsa
#print axioms EixoRiemann.projecao_iff_rh
#print axioms EixoRiemann.rhIdem_iff_weil
#print axioms EixoRiemann.somaDeQuadrados_iff
#print axioms EixoRiemann.ponte_horizontal_dlvp
#print axioms EixoRiemann.ponte_horizontal_curta
#print axioms EixoRiemann.tres_quatro_um
#print axioms EixoRiemann.positividade_aritmetica
#print axioms EixoRiemann.torcao_isometria
#print axioms EixoRiemann.torcao_troca_lados
#print axioms EixoRiemann.pontes_horizontais_finitas_e_pares
#print axioms EixoRiemann.habitante_ponte_nao_trivial
#print axioms EixoRiemann.inabitante_ponta_na_borda
#print axioms EixoRiemann.inabitante_quarteto_conectado
#print axioms EixoRiemann.inabitante_meio_da_ponte
#print axioms EixoRiemann.esqueleto_sem_amarra_inconsistente
#print axioms EixoRiemann.projecao_sem_autovalor_intermediario
