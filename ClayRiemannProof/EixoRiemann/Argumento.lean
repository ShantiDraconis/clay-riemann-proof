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
    (hav : ∀ ρ, P (v ρ) = autovalor ρ.δ • v ρ) : False := by
  have h := autovalor_colapsa (colapso P hP (hv ⟨1 / 4, 0⟩) (hav ⟨1 / 4, 0⟩))
  norm_num at h

/-- Para **qualquer** projeção (em particular a projeção ortogonal no span de `p^{−it}`, feita só com primos),
nenhum vetor não nulo tem autovalor `1/(1 + 4δ²)` com `δ ≠ 0`. Construir `P` com primos torna a idempotência
grátis e o lema do autovalor equivalente a "não existe zero fora da reta". -/
theorem projecao_sem_autovalor_intermediario {V : Type*} [AddCommGroup V] [Module ℂ V]
    (P : V →ₗ[ℂ] V) (hP : P ∘ₗ P = P) {v : V} (hv : v ≠ 0) {δ : ℝ} (hδ : δ ≠ 0) :
    P v ≠ autovalor δ • v := fun h => hδ (autovalor_colapsa (colapso P hP hv h))

/-! ## Ponte ancorada, Gram de primos e ligação -/

/-- **Ponte ancorada**: um zero de ζ na faixa. `δ` e `γ` são **calculados** de `ρ`, não são campos. -/
structure PonteAncorada where
  ρ : ℂ
  zero : riemannZeta ρ = 0
  re_pos : 0 < ρ.re
  re_lt : ρ.re < 1

noncomputable def PonteAncorada.δ (P : PonteAncorada) : ℝ := P.ρ.re - 1 / 2

/-- Com a ponte ancorada, "toda ponte tem `δ = 0`" é exatamente a `RiemannHypothesis` da Mathlib. -/
theorem ponte_ancorada_iff_rh : (∀ P : PonteAncorada, P.δ = 0) ↔ RiemannHypothesis := by
  rw [rh_iff_rhFaixa]
  constructor
  · intro h s hs
    obtain ⟨hz, h0, h1⟩ := hs
    have h' := h ⟨s, hz, h0, h1⟩
    simp only [PonteAncorada.δ] at h'
    linarith
  · intro h P
    have h' := h P.ρ ⟨P.zero, P.re_pos, P.re_lt⟩
    simp only [PonteAncorada.δ]
    linarith

noncomputable section

/-- A mesma ponte com `δ` como **campo** (ainda que com valor padrão `ρ.re − 1/2`): o campo fica solto. -/
structure PonteCampo where
  ρ : ℂ
  zero : riemannZeta ρ = 0
  re_pos : 0 < ρ.re
  re_lt : ρ.re < 1
  δ : ℝ := ρ.re - 1 / 2

end

/-- Com `δ` como campo, "toda ponte tem `δ = 0`" equivale a ζ não ter **nenhum** zero na faixa (falso, Hardy). -/
theorem ponteCampo_apaga_zeros : (∀ P : PonteCampo, P.δ = 0) ↔ Z = ∅ := by
  constructor
  · intro h
    ext s
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hz, h0, h1⟩
    have h' := h ⟨s, hz, h0, h1, 1⟩
    simp at h'
  · intro h P
    exfalso
    have hP : P.ρ ∈ Z := ⟨P.zero, P.re_pos, P.re_lt⟩
    rw [h] at hP
    simp at hP

/-- Soma de primos `Σ a_p p^{−it}`, sem nenhum zero. -/
noncomputable def somaPrimos (P : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ p ∈ P, a p * Complex.exp (-(Complex.I * t) * Real.log p)

/-- **Gram de primos é formal**: `‖Σ a_p p^{−it}‖² ≥ 0` para quaisquer coeficientes. O enunciado nem menciona ζ. -/
theorem gram_primos_formal (P : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : 0 ≤ ‖somaPrimos P a t‖ ^ 2 := by
  positivity

open ClayRiemannProof.WeilRota Filter Topology in
/-- **Ligação ⟺ RH, e por que ela é vazia**: existir **alguma** família `S_T ≥ 0` que converge para a forma de Weil
em toda função-teste é RH (critério de Weil como hipótese nomeada). Com RH, a família constante `max(W, 0)` já
serve. Todo o conteúdo estaria em uma família **específica**, feita só com primos, e que ela convirja é uma
afirmação analítica sem argumento. -/
theorem ligacao_iff_rh {F : Type*} (P : ProgramaDeWeil F) :
    (∃ S : ℝ → F → ℝ, (∀ T g, 0 ≤ S T g) ∧
      ∀ L : ℝ, 0 < L → ∀ g ∈ P.teste L, Tendsto (fun T => S T g) atTop (𝓝 (P.W g))) ↔
      RiemannHypothesis := by
  rw [P.criterio]
  constructor
  · rintro ⟨S, hS, hlim⟩ L hL g hg
    exact ge_of_tendsto' (hlim L hL g hg) (fun T => hS T g)
  · intro h
    refine ⟨fun _ g => max (P.W g) 0, fun _ _ => le_max_right _ _, ?_⟩
    intro L hL g hg
    have hm : max (P.W g) 0 = P.W g := max_eq_left (h L hL g hg)
    simp only [hm]
    exact tendsto_const_nhds

open ClayRiemannProof.WeilRota Filter Topology in
/-- **Dedução completa a partir da única hipótese em aberto**: uma família `S_T ≥ 0` que converge para a forma de
Weil dá RH e todas as formas do eixo Riemann ao mesmo tempo. -/
theorem deducao {F : Type*} (P : ProgramaDeWeil F) (S : ℝ → F → ℝ) (hS : ∀ T g, 0 ≤ S T g)
    (hlim : ∀ L : ℝ, 0 < L → ∀ g ∈ P.teste L, Tendsto (fun T => S T g) atTop (𝓝 (P.W g))) :
    RiemannHypothesis ∧ RHIdem ∧ RHQuarteto ∧ ¬ PonteHorizontal ∧ RHF ∧
      (∀ B : PonteAncorada, B.δ = 0) ∧ Nonempty Espelho := by
  have hRH := (ligacao_iff_rh P).mp ⟨S, hS, hlim⟩
  have hF := rh_iff_rhFaixa.mp hRH
  exact ⟨hRH, rhIdem_iff.mpr hF, rhQuarteto_iff.mpr hF, rh_iff_sem_ponte_horizontal.mp hF,
    rhFaixa_iff_rhF.mp hF, ponte_ancorada_iff_rh.mpr hRH, projecao_iff_rh.mpr hF⟩

/-! ## No-go do Gram de primos -/

/-- A soma de primos com coeficientes multiplicados por `c` sai multiplicada por `c`. -/
theorem somaPrimos_mul (P : Finset ℕ) (a : ℕ → ℂ) (c : ℂ) (t : ℝ) :
    somaPrimos P (fun p => c * a p) t = c * somaPrimos P a t := by
  unfold somaPrimos
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

/-- **A família de Gram é 2-homogênea**: dobrar os coeficientes multiplica `‖Σ a_p p^{−it}‖²` por 4. -/
theorem gram_dobra (P : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    ‖somaPrimos P (fun p => 2 * a p) t‖ ^ 2 = 4 * ‖somaPrimos P a t‖ ^ 2 := by
  rw [somaPrimos_mul, norm_mul]
  norm_num
  ring

open Filter Topology in
/-- **No-go da homogeneidade.** Numa classe `C` fechada por `φ ↦ 2φ`, uma família 2-homogênea (`S_T(2φ) = 4 S_T(φ)`,
como `‖Σ a_p(φ) p^{−it}‖²` ou sua média em `t`, com `a_p` linear em `φ`) só converge para um funcional 1-homogêneo
(`W(2φ) = 2 W(φ)`, como a forma de Weil, linear em `φ`) onde `W = 0`. -/
theorem gram_homogeneidade_no_go {Φ : Type*} (C : Set Φ) (dobro : Φ → Φ) (hC : ∀ φ ∈ C, dobro φ ∈ C)
    (S : ℝ → Φ → ℝ) (W : Φ → ℝ) (hS : ∀ T φ, S T (dobro φ) = 4 * S T φ)
    (hW : ∀ φ, W (dobro φ) = 2 * W φ)
    (hlim : ∀ φ ∈ C, Tendsto (fun T => S T φ) atTop (𝓝 (W φ))) : ∀ φ ∈ C, W φ = 0 := by
  intro φ hφ
  have h2 := hlim _ (hC φ hφ)
  simp only [hS] at h2
  have h4 : Tendsto (fun T => 4 * S T φ) atTop (𝓝 (4 * W φ)) := (hlim φ hφ).const_mul 4
  have he := tendsto_nhds_unique h2 h4
  rw [hW] at he
  linarith

/-- Corolário: basta **uma** função-teste com `W(φ) ≠ 0` para não existir família 2-homogênea convergindo para `W`. -/
theorem gram_no_go {Φ : Type*} (C : Set Φ) (dobro : Φ → Φ) (hC : ∀ φ ∈ C, dobro φ ∈ C) (W : Φ → ℝ)
    (hW : ∀ φ, W (dobro φ) = 2 * W φ) (hne : ∃ φ ∈ C, W φ ≠ 0) :
    ¬ ∃ S : ℝ → Φ → ℝ, (∀ T φ, S T (dobro φ) = 4 * S T φ) ∧
      ∀ φ ∈ C, Filter.Tendsto (fun T => S T φ) Filter.atTop (nhds (W φ)) := by
  rintro ⟨S, hS, hlim⟩
  obtain ⟨φ, hφ, hW0⟩ := hne
  exact hW0 (gram_homogeneidade_no_go C dobro hC S W hS hW hlim φ hφ)

/-- **Frequências cruzadas** (aritmética): para primos `p ≠ q`, `q` nunca é `n·p`. -/
theorem frequencia_cruzada_nao_inteira {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (n : ℕ) :
    q ≠ n * p := by
  intro h
  have hdvd : p ∣ q := ⟨n, by rw [h, Nat.mul_comm]⟩
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp hdvd)

/-- As frequências `log(q/p)` dos termos cruzados (`p ≠ q`) nunca são as frequências `log n` da fórmula explícita,
para nenhum `n ≥ 1`, em particular nenhuma potência de primo. A diagonal `p = q` dá `log 1 = 0`, e `n = 1` tem peso
`Λ(1) = 0` na forma de Weil (`diagonal_sem_peso`): ela não é contraexemplo. -/
theorem log_cruzado_ne_log_inteiro {p q n : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hn : 0 < n) :
    Real.log ((q : ℝ) / p) ≠ Real.log n := by
  intro h
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hdiv : (q : ℝ) / p = n :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr (div_pos hq0 hp0)) (Set.mem_Ioi.mpr hn0) h
  rw [div_eq_iff hp0.ne'] at hdiv
  have hnat : q = n * p := by exact_mod_cast hdiv
  exact frequencia_cruzada_nao_inteira hp hq hpq n hnat

/-- A diagonal do Gram tem frequência `log 1`, e `Λ(1) = 0`. -/
theorem diagonal_sem_peso : ArithmeticFunction.vonMangoldt 1 = 0 := ArithmeticFunction.vonMangoldt_apply_one

/-! ## Média em `t`: os termos cruzados somem, sobra a diagonal

Dois parâmetros diferentes: o **conjunto de primos** `P` (corte fixo) e a **janela de média** `[−T, T]` (`T → ∞`). -/

section Media

open MeasureTheory Filter Topology

theorem norm_exp_I_mul (c t : ℝ) : ‖Complex.exp (Complex.I * c * t)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem norma_integral_exp_le {c : ℝ} (hc : c ≠ 0) (T : ℝ) :
    ‖∫ t in (-T)..T, Complex.exp (Complex.I * c * t)‖ ≤ 2 / |c| := by
  have hc' : (Complex.I * c) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hc)
  rw [integral_exp_mul_complex hc', norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, div_le_div_iff_of_pos_right (abs_pos.mpr hc)]
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_exp_I_mul, norm_exp_I_mul]
  norm_num

/-- `(1/2T) ∫_{−T}^{T} e^{ict} dt → 0` para `c ≠ 0`. -/
theorem media_exp_tende_zero {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun T : ℝ => (1 / (2 * T) : ℝ) • ∫ t in (-T)..T, Complex.exp (Complex.I * c * t))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun T : ℝ => (1 / |c|) / T) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with T hT
  have hT' : T ≠ 0 := hT.ne'
  have hc0 : |c| ≠ 0 := abs_ne_zero.mpr hc
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * T))]
  calc 1 / (2 * T) * ‖∫ t in (-T)..T, Complex.exp (Complex.I * c * t)‖
      ≤ 1 / (2 * T) * (2 / |c|) := by
        gcongr
        exact norma_integral_exp_le hc T
    _ = 1 / |c| / T := by field_simp <;> ring

/-- `S(t)·conj S(t)` como soma dupla de exponenciais puras `e^{it(log q − log p)}`. -/
theorem somaPrimos_mul_conj (P : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    somaPrimos P a t * (starRingEnd ℂ) (somaPrimos P a t) =
      ∑ p ∈ P, ∑ q ∈ P, a p * (starRingEnd ℂ) (a q) *
        Complex.exp (Complex.I * ((Real.log q - Real.log p : ℝ) : ℂ) * t) := by
  unfold somaPrimos
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, ← Complex.exp_conj]
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  rw [mul_mul_mul_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **Média do Gram de primos**: com `P` fixo (primos ou quaisquer naturais positivos), a média de `|Σ a_p p^{−it}|²`
em `[−T, T]` converge para a diagonal `Σ |a_p|²`. Os termos cruzados somem; não sobra potência de primo nem termo
arquimediano. -/
theorem media_gram (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (a : ℕ → ℂ) :
    Tendsto (fun T : ℝ => (1 / (2 * T) : ℝ) •
        ∫ t in (-T)..T, somaPrimos P a t * (starRingEnd ℂ) (somaPrimos P a t))
      atTop (𝓝 (∑ p ∈ P, a p * (starRingEnd ℂ) (a p))) := by
  have hint : ∀ T : ℝ, (∫ t in (-T)..T, somaPrimos P a t * (starRingEnd ℂ) (somaPrimos P a t)) =
      ∑ p ∈ P, ∑ q ∈ P, a p * (starRingEnd ℂ) (a q) *
        ∫ t in (-T)..T, Complex.exp (Complex.I * ((Real.log q - Real.log p : ℝ) : ℂ) * t) := by
    intro T
    simp_rw [somaPrimos_mul_conj]
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun p _ => ?_
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun q _ => ?_
        exact intervalIntegral.integral_const_mul _ _
      · intro q _
        apply Continuous.intervalIntegrable
        fun_prop
    · intro p _
      apply Continuous.intervalIntegrable
      fun_prop
  have htarget : (∑ p ∈ P, a p * (starRingEnd ℂ) (a p)) =
      ∑ p ∈ P, ∑ q ∈ P, (if p = q then a p * (starRingEnd ℂ) (a q) else 0) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    simp [hp]
  simp_rw [hint, Finset.smul_sum]
  rw [htarget]
  refine tendsto_finsetSum _ fun p hp => tendsto_finsetSum _ fun q hq => ?_
  by_cases hpq : p = q
  · subst hpq
    rw [if_pos rfl]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    simp only [sub_self, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const, Complex.real_smul]
    push_cast
    first
      | (field_simp; ring)
      | field_simp
      | ring
  · rw [if_neg hpq]
    have hc : Real.log q - Real.log p ≠ 0 := by
      intro h
      apply hpq
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hP p hp
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hP q hq
      have h' : Real.log (q : ℝ) = Real.log (p : ℝ) := by linarith
      have := Real.log_injOn_pos (Set.mem_Ioi.mpr hq0) (Set.mem_Ioi.mpr hp0) h'
      exact_mod_cast this.symm
    have h := (media_exp_tende_zero hc).const_mul (a p * (starRingEnd ℂ) (a q))
    rw [mul_zero] at h
    refine h.congr fun T => ?_
    rw [mul_smul_comm]

end Media

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
#print axioms EixoRiemann.ponte_ancorada_iff_rh
#print axioms EixoRiemann.ponteCampo_apaga_zeros
#print axioms EixoRiemann.gram_primos_formal
#print axioms EixoRiemann.ligacao_iff_rh
#print axioms EixoRiemann.deducao
#print axioms EixoRiemann.gram_dobra
#print axioms EixoRiemann.gram_homogeneidade_no_go
#print axioms EixoRiemann.gram_no_go
#print axioms EixoRiemann.frequencia_cruzada_nao_inteira
#print axioms EixoRiemann.log_cruzado_ne_log_inteiro
#print axioms EixoRiemann.diagonal_sem_peso
#print axioms EixoRiemann.media_exp_tende_zero
#print axioms EixoRiemann.somaPrimos_mul_conj
#print axioms EixoRiemann.media_gram
