import ClayRiemannProof.Meio
import ClayRiemannProof.PorQueMeio
import ClayRiemannProof.Identidades

/-!
# Os três estados (esquerda, meio, direita), o empate de `π` e `Γ` no meio, e a forma de uma prova incondicional

1. **Os três estados** (`Estado`, `classifica`): `esq` (`Re s < ½`), `meio` (`Re s = ½`), `dir` (`Re s > ½`). O "2"
   da conversa é o `meio`: não é "verdadeiro e falso ao mesmo tempo", é a posição da reta. `classifica_torcao`: o
   espelho `s ↦ 1 − s̄` troca `esq` com `dir` e fixa o `meio`. `quem_fixa_o_que`: a meia volta `s ↦ 1 − s` fixa só o
   **ponto** ½; quem fixa a **reta** é `s ↦ 1 − s̄`.
2. **O empate no meio** (`chi_meio`): com `χ(s) = 2(2π)^{−s}Γ(s)cos(πs/2)`, a equação funcional da Mathlib é
   `ζ(1 − s) = χ(s)ζ(s)` (`zeta_um_menos`), e `|χ(½ + it)| = 1` para todo `t`. Prova: `χ(s)χ(1 − s) = 1` pela
   reflexão `Γ(s)Γ(1 − s) = π/sin(πs)` (`chi_mul_chi_um_menos`), e `χ(1 − s) = conj χ(s)` na reta (`chi_conj`). Mas
   `equacao_propaga`: a equação leva zero em zero (`0 = χ·0`); ela não proíbe o par `σ`, `1 − σ`.
3. **A conjuntura** (`pior_caso`): cada par tem pior lado `max(Re ρ, 1 − Re ρ) ≥ ½`, com igualdade só no meio; o erro
   dos primos é governado por esse pior lado. `conjuntura_fixada_pelo_meio`: com a equivalência de von Koch como
   hipótese nomeada, "todo zero no meio" ⟺ `|ψ(x) − x| ≤ C√x·log²x`.
4. **A forma de uma prova incondicional** (`forma_por_aproximacao`): se há conjuntos `W n` (os zeros de aproximações
   feitas com finitos primos) todos na reta, e todo zero de `ζ` é limite de pontos deles, vale a RH. E
   `o_que_a_prova_nao_pode_ser`: só a estrutura, só `π`, `Γ` e `ζ` com a simetria, só a proporção, ou só o empate
   local não bastam.

Nada aqui prova RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.TresEstados

open Complex ComplexConjugate Filter Topology ClayRiemannProof.Zeta.Symmetry

/-! ## 1. Os três estados -/

/-- As três posições de um ponto da faixa em relação à reta. -/
inductive Estado : Type
  | esq : Estado
  | meio : Estado
  | dir : Estado
  deriving DecidableEq

/-- Em que estado está `s`. -/
noncomputable def classifica (s : ℂ) : Estado :=
  if s.re < 1 / 2 then .esq else if s.re = 1 / 2 then .meio else .dir

/-- O espelho dos estados: troca os lados, fixa o meio. -/
def troca : Estado → Estado
  | .esq => .dir
  | .meio => .meio
  | .dir => .esq

theorem troca_troca (e : Estado) : troca (troca e) = e := by
  cases e <;> rfl

theorem classifica_meio_iff (s : ℂ) : classifica s = .meio ↔ s.re = 1 / 2 := by
  unfold classifica
  by_cases h1 : s.re < 1 / 2
  · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
    exact ⟨fun h => (by cases h), fun h => (by linarith)⟩
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
    by_cases h2 : s.re = 1 / 2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)]
      exact ⟨fun _ => h2, fun _ => rfl⟩
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]
      exact ⟨fun h => (by cases h), fun h => absurd h h2⟩

/-- **O espelho `s ↦ 1 − s̄` troca os lados e fixa o meio.** -/
theorem classifica_torcao (s : ℂ) : classifica (torcao s) = troca (classifica s) := by
  unfold classifica
  rw [re_torcao]
  by_cases h1 : s.re < 1 / 2
  · have h3 : ¬ (1 - s.re < 1 / 2) := by linarith
    have h4 : ¬ (1 - s.re = 1 / 2) := by
      intro e
      linarith
    rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_right_of_eq_false _ _ (eq_false h3), ite_eq_right_of_eq_false _ _ (eq_false h4)]
    rfl
  · by_cases h2 : s.re = 1 / 2
    · have h3 : ¬ (1 - s.re < 1 / 2) := by linarith
      have h4 : 1 - s.re = 1 / 2 := by linarith
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_left_of_eq_true _ _ (eq_true h2), ite_eq_right_of_eq_false _ _ (eq_false h3), ite_eq_left_of_eq_true _ _ (eq_true h4)]
      rfl
    · have h4 : 1 - s.re < 1 / 2 := by
        rcases lt_or_gt_of_ne h2 with h | h
        · exact absurd h h1
        · linarith
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h2), ite_eq_left_of_eq_true _ _ (eq_true h4)]
      rfl

/-- **Quem fixa o quê**: `s ↦ 1 − s` fixa só o ponto ½; `s ↦ 1 − s̄` fixa a reta, que é o estado `meio`. -/
theorem quem_fixa_o_que (s : ℂ) : (tensao s = s ↔ s = 1 / 2) ∧ (torcao s = s ↔ s.re = 1 / 2) ∧
    (torcao s = s ↔ classifica s = .meio) :=
  ⟨tensao_fixo_iff s, torcao_fixo_iff s, (torcao_fixo_iff s).trans (classifica_meio_iff s).symm⟩

/-! ## 2. O empate de `π` e `Γ` no meio -/

/-- O fator da equação funcional: `ζ(1 − s) = χ(s)ζ(s)`. -/
noncomputable def chi (s : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2)

/-- **A equação funcional** (Mathlib): `ζ(1 − s) = χ(s)ζ(s)`. -/
theorem zeta_um_menos {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) = chi s * riemannZeta s := by
  rw [riemannZeta_one_sub hs hs']
  rfl

/-- **A equação leva zero em zero**: `0 = χ·0`. Ela cria o gêmeo `1 − s`; não proíbe o par. -/
theorem equacao_propaga {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) (h : riemannZeta s = 0) :
    riemannZeta (1 - s) = 0 := by
  rw [zeta_um_menos hs hs', h, mul_zero]

theorem sin_meio_ne_zero (t : ℝ) : Complex.sin ((Real.pi : ℂ) * (1 / 2 + t * I)) ≠ 0 := by
  rw [Ne, Complex.sin_eq_zero_iff]
  rintro ⟨k, hk⟩
  have h1 : ((Real.pi : ℂ) * (1 / 2 + t * I)).re = Real.pi / 2 := by
    simp [Complex.mul_re, div_eq_mul_inv]
  have h2 : ((k : ℂ) * (Real.pi : ℂ)).re = k * Real.pi := by
    simp [Complex.mul_re]
  have h3 : Real.pi / 2 = k * Real.pi := by rw [← h1, ← h2, hk]
  have hpi := Real.pi_pos
  have h4 : (2 * k : ℝ) = 1 := by
    have : Real.pi * (2 * k - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · linarith
  have h5 : (2 * k : ℤ) = 1 := by exact_mod_cast h4
  omega

theorem dois_pi_ne_zero : (2 * (Real.pi : ℂ)) ≠ 0 :=
  mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)

/-- **`χ(s)χ(1 − s) = 1` na reta**, pela reflexão `Γ(s)Γ(1 − s) = π/sin(πs)`. -/
theorem chi_mul_chi_um_menos (t : ℝ) : chi (1 / 2 + t * I) * chi (1 - (1 / 2 + t * I)) = 1 := by
  set s : ℂ := 1 / 2 + t * I with hs
  have hsin : Complex.sin ((Real.pi : ℂ) * s) ≠ 0 := sin_meio_ne_zero t
  have hG := Complex.Gamma_mul_Gamma_one_sub s
  have hcos : Complex.cos ((Real.pi : ℂ) * (1 - s) / 2) = Complex.sin ((Real.pi : ℂ) * s / 2) := by
    rw [show (Real.pi : ℂ) * (1 - s) / 2 = (Real.pi : ℂ) / 2 - (Real.pi : ℂ) * s / 2 by ring,
      Complex.cos_pi_div_two_sub]
  have hsin2 : Complex.sin ((Real.pi : ℂ) * s) =
      2 * Complex.sin ((Real.pi : ℂ) * s / 2) * Complex.cos ((Real.pi : ℂ) * s / 2) := by
    rw [← Complex.sin_two_mul]
    congr 1
    ring
  have hpow : (2 * (Real.pi : ℂ)) ^ (-s) * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) = (2 * (Real.pi : ℂ))⁻¹ := by
    rw [← Complex.cpow_add _ _ dois_pi_ne_zero, show -s + -(1 - s) = (-1 : ℂ) by ring, Complex.cpow_neg_one]
  have hs2 : Complex.sin ((Real.pi : ℂ) * s / 2) ≠ 0 := fun h => hsin (by rw [hsin2, h]; ring)
  have hc2 : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := fun h => hsin (by rw [hsin2, h]; ring)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold chi
  rw [hcos]
  calc 2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2) *
        (2 * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) * Complex.Gamma (1 - s) * Complex.sin ((Real.pi : ℂ) * s / 2))
      = 4 * ((2 * (Real.pi : ℂ)) ^ (-s) * (2 * (Real.pi : ℂ)) ^ (-(1 - s))) *
          (Complex.Gamma s * Complex.Gamma (1 - s)) *
          (Complex.cos ((Real.pi : ℂ) * s / 2) * Complex.sin ((Real.pi : ℂ) * s / 2)) := by ring
    _ = 4 * (2 * (Real.pi : ℂ))⁻¹ * ((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * s)) *
          (Complex.cos ((Real.pi : ℂ) * s / 2) * Complex.sin ((Real.pi : ℂ) * s / 2)) := by rw [hpow, hG]
    _ = 1 := by
          rw [hsin2]
          field_simp
          ring

/-- **`χ` comuta com a conjugação**: `conj χ(s) = χ(s̄)`. -/
theorem chi_conj (s : ℂ) : conj (chi s) = chi (conj s) := by
  have harg : (2 * (Real.pi : ℂ)).arg ≠ Real.pi := by
    rw [show (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_ne_zero.symm
  have hA : conj ((2 * (Real.pi : ℂ)) ^ (-s)) = (2 * (Real.pi : ℂ)) ^ (-conj s) := by
    have h := Complex.conj_cpow (2 * (Real.pi : ℂ)) (-conj s) harg
    rw [map_neg, Complex.conj_conj] at h
    rw [← h]
    congr 1
    rw [map_mul, map_ofNat, Complex.conj_ofReal]
  have hC : conj (Complex.cos ((Real.pi : ℂ) * s / 2)) = Complex.cos ((Real.pi : ℂ) * conj s / 2) := by
    rw [← Complex.cos_conj]
    congr 1
    rw [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal]
  unfold chi
  rw [map_mul, map_mul, map_mul, hA, hC, ← Complex.Gamma_conj, map_ofNat]

/-- **No meio, `π` e `Γ` empatam**: `|χ(½ + it)| = 1` para todo `t`. -/
theorem chi_meio (t : ℝ) : ‖chi (1 / 2 + t * I)‖ = 1 := by
  have h1 := chi_mul_chi_um_menos t
  have hc : (1 : ℂ) - (1 / 2 + t * I) = conj (1 / 2 + t * I) := by
    apply Complex.ext <;> norm_num
  rw [hc, ← chi_conj, Complex.mul_conj] at h1
  have h2 : Complex.normSq (chi (1 / 2 + t * I)) = 1 := by exact_mod_cast h1
  rw [Complex.normSq_eq_norm_sq] at h2
  have h0 := norm_nonneg (chi (1 / 2 + t * I))
  nlinarith

/-! ## 3. A conjuntura -/

/-- **O pior lado de cada par**: `max(Re ρ, 1 − Re ρ) ≥ ½`, com igualdade só no meio. -/
theorem pior_caso (ρ : ℂ) :
    1 / 2 ≤ max ρ.re (1 - ρ.re) ∧ (max ρ.re (1 - ρ.re) = 1 / 2 ↔ classifica ρ = .meio) := by
  rw [classifica_meio_iff]
  refine ⟨?_, ⟨fun h => ?_, fun h => ?_⟩⟩
  · rcases le_total ρ.re (1 / 2) with h | h
    · exact le_max_of_le_right (by linarith)
    · exact le_max_of_le_left h
  · have h1 := le_max_left ρ.re (1 - ρ.re)
    have h2 := le_max_right ρ.re (1 - ρ.re)
    linarith
  · rw [h]
    norm_num

/-- **A conjuntura dos primos é fixada pelo meio** (com a equivalência de von Koch como hipótese nomeada): todo zero
no estado `meio` ⟺ `|ψ(x) − x| ≤ C√x·log²x`. -/
theorem conjuntura_fixada_pelo_meio (h : Identidades.VonKoch1901) :
    (∀ ρ ∈ Z, classifica ρ = .meio) ↔
      ∃ C : ℝ, ∀ x : ℕ, 2 ≤ x → |Identidades.psi x - x| ≤ C * Real.sqrt x * Real.log x ^ 2 := by
  unfold Identidades.VonKoch1901 at h
  rw [← h, PorQueMeio.rh_iff_reta]
  exact forall₂_congr fun ρ _ => classifica_meio_iff ρ

/-! ## 4. A forma de uma prova incondicional -/

/-- **A forma por aproximação**: se os conjuntos `W n` (os zeros de aproximações construídas com finitos primos) estão
todos na reta, e todo zero não trivial de `ζ` é limite de pontos `w n ∈ W n`, então vale a RH. As duas hipóteses são
o trabalho inteiro: a primeira é uma positividade para cada aproximação; a segunda é a convergência (com convergência
uniforme, o teorema de Hurwitz a dá). -/
theorem forma_por_aproximacao {W : ℕ → Set ℂ} (hW : ∀ n, ∀ w ∈ W n, w.re = 1 / 2)
    (hlim : ∀ ρ ∈ Z, ∃ w : ℕ → ℂ, (∀ n, w n ∈ W n) ∧ Tendsto w atTop (𝓝 ρ)) : RiemannHypothesis := by
  rw [PorQueMeio.rh_iff_reta]
  intro ρ hρ
  obtain ⟨w, hw, ht⟩ := hlim ρ hρ
  have h : Tendsto (fun n => (w n).re) atTop (𝓝 ρ.re) := (Complex.continuous_re.tendsto ρ).comp ht
  have hc : (fun n => (w n).re) = fun _ => (1 / 2 : ℝ) := funext fun n => hW n (w n) (hw n)
  rw [hc] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- **O que a prova não pode ser**: só a estrutura (faixa, `1 − s`, `s̄`, altura `> 13`) não decide; `π`, `Γ` e o
próprio `ζ` com a simetria não decidem (`ξ·P` tem um quarteto fora); 100% de proporção não decide; e o empate local
`|χ| = 1` no meio convive com a equação funcional levando qualquer zero no seu gêmeo. -/
theorem o_que_a_prova_nao_pode_ser :
    (¬ ∀ W : Set ℂ, Estrutura.EstruturaDeRiemann W → ∀ ρ ∈ W, ρ.re = 1 / 2) ∧
    (∃ f : ℂ → ℂ, Analogs.Simetrica f ∧ (∀ w, Analogs.xiW w = 0 → f w = 0) ∧ ∃ w : ℂ, f w = 0 ∧ w.re ≠ 0) ∧
    (∃ W : Set ℂ, Estrutura.EstruturaDeRiemann W ∧ Tendsto (Proporcao.proporcao W) atTop (𝓝 1) ∧
      ∃ ρ ∈ W, ρ.re ≠ 1 / 2) ∧
    ((∀ t : ℝ, ‖chi (1 / 2 + t * I)‖ = 1) ∧
      ∀ s : ℂ, (∀ n : ℕ, s ≠ -n) → s ≠ 1 → riemannZeta s = 0 → riemannZeta (1 - s) = 0) :=
  ⟨Estrutura.estrutura_nao_decide, Meio.ingredientes_nao_bastam, Proporcao.cem_por_cento_nao_basta,
    chi_meio, fun _ hs hs' h => equacao_propaga hs hs' h⟩

end ClayRiemannProof.TresEstados
