import ClayRiemannProof.EixoRiemann.Argumento

/-!
# Mapa do eixo Riemann: tronco, galhos, becos e bases

Cada argumento derivado vira um teorema nomeado, com a dependência explícita no enunciado.

## Tronco (condicional à única hipótese em aberto)
`tronco_positividade`: família `S_T ≥ 0` convergindo para `W` ⟹ `W ≥ 0` nas funções-teste.
`tronco_weil_rh`: `W ≥ 0` ⟹ `RiemannHypothesis` (critério de Weil, hipótese nomeada `ProgramaDeWeil`).

## Galhos (de `RiemannHypothesis`)
`galho_ponte_ancorada`, `galho_ponte_segura`, `galho_Q`, `galho_F`, `galho_sem_horizontal`, `galho_espelho`,
`galho_somaDeQuadrados`. O sentido contrário, RH falsa, é `rh_falsa_da_quarteto`: existe um zero fora da reta
cujo quarteto tem 4 pontos, soma 2 em `N(T)` e carrega a ponte horizontal `ρ → 1 − ρ̄`.

## Bases clássicas como hipóteses nomeadas
`Hardy1914` (infinitos zeros na reta): `hardy_refuta_ponteCampo`, `hardy_refuta_rhIdemProposta`.
`PlattTrudgian2021`: `pontes_verticais_platt_trudgian`, toda ponte até `3 000 175 332 800` é vertical.

## Aritmética da "dobragem" de razões (incondicional)
`vonMangoldt_mul_primos_distintos`: `Λ(pq) = 0` para `p ≠ q`. `vonMangoldt_quadrado_primo`: `Λ(p²) = log p`.
`produto_nao_primo`: `pq` nunca é primo. Os pares de primos geram as frequências `log(q/p)` (nunca `log n`),
`log(pq)` (peso 0 se `p ≠ q`) e `log p²`; a frequência `log p`, termo principal dos primos, nunca aparece.
-/

open ClayRiemannProof.Zeta.Symmetry

namespace EixoRiemann

/-! ## Tronco -/

open ClayRiemannProof.WeilRota Filter Topology in
theorem tronco_positividade {F : Type*} (P : ProgramaDeWeil F) (S : ℝ → F → ℝ) (hS : ∀ T g, 0 ≤ S T g)
    (hlim : ∀ L : ℝ, 0 < L → ∀ g ∈ P.teste L, Tendsto (fun T => S T g) atTop (𝓝 (P.W g))) :
    ∀ L : ℝ, 0 < L → ∀ g ∈ P.teste L, 0 ≤ P.W g :=
  fun L hL g hg => ge_of_tendsto' (hlim L hL g hg) (fun T => hS T g)

open ClayRiemannProof.WeilRota in
theorem tronco_weil_rh {F : Type*} (P : ProgramaDeWeil F)
    (hW : ∀ L : ℝ, 0 < L → ∀ g ∈ P.teste L, 0 ≤ P.W g) : RiemannHypothesis :=
  P.criterio.mpr hW

/-! ## Galhos -/

theorem galho_ponte_ancorada (h : RiemannHypothesis) : ∀ B : PonteAncorada, B.δ = 0 :=
  ponte_ancorada_iff_rh.mpr h

theorem galho_ponte_segura (h : RiemannHypothesis) : RHIdem := rh_iff_rhIdem.mp h

theorem galho_Q (h : RiemannHypothesis) : RHQuarteto := rhQuarteto_iff.mpr (rh_iff_rhFaixa.mp h)

theorem galho_F (h : RiemannHypothesis) : RHF := rhFaixa_iff_rhF.mp (rh_iff_rhFaixa.mp h)

theorem galho_sem_horizontal (h : RiemannHypothesis) : ¬ PonteHorizontal :=
  rh_iff_sem_ponte_horizontal.mp (rh_iff_rhFaixa.mp h)

theorem galho_espelho (h : RiemannHypothesis) : Nonempty Espelho := projecao_iff_rh.mpr (rh_iff_rhFaixa.mp h)

open ClayRiemannProof.WeilRota in
theorem galho_somaDeQuadrados {F : Type*} (P : ProgramaDeWeil F) (h : RiemannHypothesis) :
    ∀ L : ℝ, 0 < L → ∀ g ∈ P.teste L, ∃ c : ℝ, P.W g = c ^ 2 :=
  (somaDeQuadrados_iff P).mpr (galho_ponte_segura h)

/-- **RH falsa, em pontes**: existe um zero fora da reta; o seu quarteto tem 4 pontos, soma 2 em `N(T)`, e ele carrega
a ponte horizontal `ρ → 1 − ρ̄`. -/
theorem rh_falsa_da_quarteto (h : ¬ RiemannHypothesis) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ (orbita ρ).card = 4 ∧
      ((orbita ρ).filter (fun x => 0 < x.im)).card = 2 ∧
      Idem.aplica riemannZeta ⟨ρ, ((1 - 2 * ρ.re : ℝ) : ℂ)⟩ = ⟨0, 0⟩ := by
  rw [rh_iff_rhFaixa] at h
  unfold RHFaixa at h
  push_neg at h
  obtain ⟨ρ, hρ, hre⟩ := h
  have him := im_ne_zero_of_mem_Z hρ
  exact ⟨ρ, hρ, hre, orbita_card hre him, orbita_metade_de_cima hre him, ponte_horizontal_do_quarteto hρ⟩

/-! ## Bases clássicas como hipóteses nomeadas -/

/-- Hardy (1914): infinitos zeros na reta crítica. Teorema publicado, fora da Mathlib. -/
def Hardy1914 : Prop := {s : ℂ | s ∈ Z ∧ s.re = 1 / 2}.Infinite

theorem Z_nonempty_de_hardy (h : Hardy1914) : Z.Nonempty := by
  obtain ⟨s, hs⟩ := h.nonempty
  exact ⟨s, hs.1⟩

/-- Com Hardy, a ponte com `δ` como campo é refutada. -/
theorem hardy_refuta_ponteCampo (h : Hardy1914) : ¬ ∀ P : PonteCampo, P.δ = 0 := by
  intro hP
  obtain ⟨s, hs⟩ := Z_nonempty_de_hardy h
  rw [ponteCampo_apaga_zeros.mp hP] at hs
  simp at hs

/-- Com Hardy, a RH-Idem proposta (`δ = 0` obrigatório) é refutada. -/
theorem hardy_refuta_rhIdemProposta (h : Hardy1914) : ¬ RHIdemProposta := by
  intro hP
  obtain ⟨s, hs⟩ := Z_nonempty_de_hardy h
  rw [rhIdemProposta_implica_sem_zeros hP] at hs
  simp at hs

/-- Com Platt–Trudgian (2021), toda ponte com as duas pontas em `|Im| ≤ 3 000 175 332 800` é vertical. -/
theorem pontes_verticais_platt_trudgian (h : ClayRiemannProof.FiniteWorlds.PlattTrudgian2021) :
    RHIdemAte 3000175332800 :=
  rhIdemAte_of_rhateZ (T := 3000175332800) h

/-! ## Aritmética da dobragem de razões -/

theorem vonMangoldt_mul_primos_distintos {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ArithmeticFunction.vonMangoldt (p * q) = 0 := by
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff, isPrimePow_nat_iff]
  rintro ⟨r, k, hr, -, h⟩
  have hpd : p ∣ r := hp.dvd_of_dvd_pow (show p ∣ r ^ k by rw [h]; exact dvd_mul_right p q)
  have hqd : q ∣ r := hq.dvd_of_dvd_pow (show q ∣ r ^ k by rw [h]; exact dvd_mul_left q p)
  exact hpq (((Nat.prime_dvd_prime_iff_eq hp hr).mp hpd).trans ((Nat.prime_dvd_prime_iff_eq hq hr).mp hqd).symm)

theorem vonMangoldt_quadrado_primo {p : ℕ} (hp : p.Prime) :
    ArithmeticFunction.vonMangoldt (p ^ 2) = Real.log p := by
  rw [ArithmeticFunction.vonMangoldt_apply_pow two_ne_zero, ArithmeticFunction.vonMangoldt_apply_prime hp]

theorem produto_nao_primo {p q : ℕ} (hp : p.Prime) (hq : q.Prime) : ¬ (p * q).Prime :=
  Nat.not_prime_mul hp.one_lt.ne' hq.one_lt.ne'

end EixoRiemann

#print axioms EixoRiemann.tronco_positividade
#print axioms EixoRiemann.tronco_weil_rh
#print axioms EixoRiemann.galho_ponte_ancorada
#print axioms EixoRiemann.galho_ponte_segura
#print axioms EixoRiemann.galho_Q
#print axioms EixoRiemann.galho_F
#print axioms EixoRiemann.galho_sem_horizontal
#print axioms EixoRiemann.galho_espelho
#print axioms EixoRiemann.galho_somaDeQuadrados
#print axioms EixoRiemann.rh_falsa_da_quarteto
#print axioms EixoRiemann.Z_nonempty_de_hardy
#print axioms EixoRiemann.hardy_refuta_ponteCampo
#print axioms EixoRiemann.hardy_refuta_rhIdemProposta
#print axioms EixoRiemann.pontes_verticais_platt_trudgian
#print axioms EixoRiemann.vonMangoldt_mul_primos_distintos
#print axioms EixoRiemann.vonMangoldt_quadrado_primo
#print axioms EixoRiemann.produto_nao_primo
