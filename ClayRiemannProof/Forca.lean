import ClayRiemannProof.Colisao
import ClayRiemannProof.Analogs

/-!
# A força mínima que tira um par de zeros da reta

Na reta, `ζ(½ + it) = e^{−iθ(t)} Z(t)` com `Z` real. Entre dois zeros vizinhos `γ₁ < γ₂`, `Z` tem uma lombada de
altura `a = |Z(t*)|`; perto de um par apertado, `Z(t) ≈ a − c(t − m)²` com `c = |Z''|/2`. Um empurrão vertical `ε`
que preserve a equação funcional (Z continua real na reta) troca a lombada por `(a − ε) − c(t − m)²`:

* `lombada_reais_iff`: os zeros continuam todos reais (na reta) **exatamente** enquanto `ε ≤ a`. A força mínima é a
  altura da lombada.
* `par_fora_da_reta`: passado o limiar, os zeros são `m ± ib`, `b = √((ε − a)/c) = √(2(ε − |Z*|)/|Z''|)`; em
  `s = ½ + it` isso é o par `½ ∓ b + im`, fora da reta e simétrico pela torção (com a conjugação, o quarteto).
  É a lei da raiz quadrada (`Colisao.raiz_quadrada`) com o empurrão no lugar do tempo.
* `lombada_do_par`, `limiar_do_par`: no modelo do par, `Z = c(t − γ₁)(γ₂ − t)`, a lombada tem altura `cΔ²/4`
  (= `|Z''|Δ²/8`): o limiar é `ε* = cΔ²/4`.
* `calor_eh_empurrao`: no fluxo de de Bruijn do par isolado (`Colisao.H2`), voltar o tempo de `|t|` é o mesmo que
  empurrar `2|t|`: `H_t = H_0 − 2t`. As duas forças são a mesma, medidas em unidades diferentes.
* `empurrao_simetrico`, `zeta_empurrada_quarteto`: empurrar `ξ(½ + w)` por `ε·g(w)` com `g` simétrico (`g(−w) = g(w)`,
  `g(w̄) = conj g(w)`; por exemplo `g = 1`, `constante_simetrica`) preserva as duas simetrias, e os zeros da função
  empurrada vêm em quartetos `w, −w, w̄, −w̄`: mudar `Z` na escala do próprio `Z` tira zeros da reta, mas sempre aos
  quatro.
* `menos_forca`: lombada mais baixa, limiar menor: o ponto mais fácil é o de menor `|Z*|`, que não é
  necessariamente o par mais apertado (o par mais apertado tem o menor tempo do calor `Δ²/8`, mas pode ter `|Z''|`
  grande).

As alturas `|Z*|` dos pares medidos vêm de Riemann–Siegel (estimativa) e da Arb (bolas certificadas), fora do kernel
(`computations/forca/`, README seção 27). Nada aqui prova ou refuta RH: é a medida de quão perto `ζ` está, em cada
ponto, de uma função com as mesmas simetrias e um zero fora da reta. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Forca

open Complex ComplexConjugate

/-- **Lombada empurrada**: `(a − ε) − c·(w − m)²` (altura `a`, curvatura `c`, centro `m`, empurrão `ε`). -/
def lombada (a c m ε : ℝ) (w : ℂ) : ℂ := ((a - ε : ℝ) : ℂ) - (c : ℂ) * (w - (m : ℂ)) ^ 2

/-- Um complexo cujo quadrado é real `≥ 0` é real. -/
theorem im_eq_zero_of_sq {z : ℂ} {r : ℝ} (hr : 0 ≤ r) (h : z ^ 2 = (r : ℂ)) : z.im = 0 := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  rw [sq] at hre him
  simp only [mul_re, mul_im, ofReal_re, ofReal_im] at hre him
  by_contra hy
  have hx : z.re = 0 := by
    have h0 : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact h1
    · exact absurd h1 hy
  rw [hx] at hre
  have : 0 < z.im * z.im := mul_self_pos.mpr hy
  linarith

/-- **Limiar exato**: os zeros da lombada empurrada são todos reais se e só se `ε ≤ a`. -/
theorem lombada_reais_iff {a c m ε : ℝ} (hc : 0 < c) :
    (∀ w : ℂ, lombada a c m ε w = 0 → w.im = 0) ↔ ε ≤ a := by
  have hc' : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    set b : ℝ := Real.sqrt ((ε - a) / c) with hb
    have hpos : 0 < (ε - a) / c := div_pos (by linarith) hc
    have hsq : ((b : ℝ) : ℂ) ^ 2 = (((ε - a) / c : ℝ) : ℂ) := by
      rw [← ofReal_pow, hb, Real.sq_sqrt hpos.le]
    have hz : lombada a c m ε ((m : ℂ) + I * (b : ℂ)) = 0 := by
      unfold lombada
      rw [add_sub_cancel_left, mul_pow, hsq, I_sq]
      push_cast
      first
        | (field_simp; ring)
        | field_simp
    have him := h _ hz
    simp only [add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, zero_mul, one_mul, zero_add] at him
    exact (Real.sqrt_pos.mpr hpos).ne' him
  · intro hle w hw
    have h2 : (w - (m : ℂ)) ^ 2 = (((a - ε) / c : ℝ) : ℂ) := by
      unfold lombada at hw
      push_cast at hw ⊢
      rw [eq_div_iff hc']
      linear_combination -hw
    have := im_eq_zero_of_sq (div_nonneg (by linarith) hc.le) h2
    simpa using this

/-- **Passado o limiar**: `m ± ib` são zeros, `b = √((ε − a)/c) > 0`, e em `s = ½ + iw` são `½ ∓ b + im`. -/
theorem par_fora_da_reta {a c m ε : ℝ} (hc : 0 < c) (hε : a < ε) :
    lombada a c m ε ((m : ℂ) + I * (Real.sqrt ((ε - a) / c) : ℂ)) = 0 ∧
      lombada a c m ε ((m : ℂ) - I * (Real.sqrt ((ε - a) / c) : ℂ)) = 0 ∧
      0 < Real.sqrt ((ε - a) / c) ∧
      (1 / 2 + I * ((m : ℂ) + I * (Real.sqrt ((ε - a) / c) : ℂ))).re = 1 / 2 - Real.sqrt ((ε - a) / c) ∧
      (1 / 2 + I * ((m : ℂ) - I * (Real.sqrt ((ε - a) / c) : ℂ))).re = 1 / 2 + Real.sqrt ((ε - a) / c) := by
  have hpos : 0 < (ε - a) / c := div_pos (by linarith) hc
  have hsq : ((Real.sqrt ((ε - a) / c) : ℝ) : ℂ) ^ 2 = (((ε - a) / c : ℝ) : ℂ) := by
    rw [← ofReal_pow, Real.sq_sqrt hpos.le]
  have hc' : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  refine ⟨?_, ?_, Real.sqrt_pos.mpr hpos, ?_, ?_⟩
  · unfold lombada
    rw [add_sub_cancel_left, mul_pow, hsq, I_sq]
    push_cast
    first
      | (field_simp; ring)
      | field_simp
  · unfold lombada
    rw [sub_sub_cancel_left, neg_pow, mul_pow, hsq, I_sq]
    push_cast
    first
      | (field_simp; ring)
      | field_simp
  · first
      | (simp; done)
      | (simp; norm_num; done)
      | (simp; ring)
  · first
      | (simp; done)
      | (simp; norm_num; done)
      | (simp; ring)

/-- **O modelo do par**: `c(w − γ₁)(γ₂ − w)` é a lombada de altura `c(γ₂ − γ₁)²/4` centrada no ponto médio. -/
theorem lombada_do_par (γ₁ γ₂ c ε : ℝ) (w : ℂ) :
    (c : ℂ) * (w - γ₁) * (γ₂ - w) - ε = lombada (c * (γ₂ - γ₁) ^ 2 / 4) c ((γ₁ + γ₂) / 2) ε w := by
  unfold lombada
  push_cast
  ring

/-- **Limiar do par**: o empurrão `ε` tira o par da reta exatamente quando passa de `c(γ₂ − γ₁)²/4 = |Z''|Δ²/8`. -/
theorem limiar_do_par {γ₁ γ₂ c ε : ℝ} (hc : 0 < c) :
    (∀ w : ℂ, (c : ℂ) * (w - γ₁) * (γ₂ - w) - ε = 0 → w.im = 0) ↔ ε ≤ c * (γ₂ - γ₁) ^ 2 / 4 := by
  simp only [lombada_do_par]
  exact lombada_reais_iff hc

/-- **Voltar o tempo do calor é empurrar**: `H_t = H_0 − 2t` (o tempo `t < 0` empurra `2|t|`). -/
theorem calor_eh_empurrao (a t : ℝ) (z : ℂ) :
    ClayRiemannProof.Colisao.H2 a t z = ClayRiemannProof.Colisao.H2 a 0 z - 2 * (t : ℂ) := by
  unfold ClayRiemannProof.Colisao.H2
  push_cast
  ring

/-- **Lombada mais baixa, limiar menor**: o empurrão que tira da reta o par da lombada mais alta tira também o da
mais baixa. -/
theorem menos_forca {a₁ a₂ c m ε : ℝ} (hc : 0 < c) (h : a₁ ≤ a₂)
    (h₂ : ∃ w : ℂ, lombada a₂ c m ε w = 0 ∧ w.im ≠ 0) : ∃ w : ℂ, lombada a₁ c m ε w = 0 ∧ w.im ≠ 0 := by
  obtain ⟨w, hw, hne⟩ := h₂
  have hε : a₂ < ε := by
    by_contra hle
    push_neg at hle
    exact hne ((lombada_reais_iff hc).mpr hle w hw)
  obtain ⟨h0, -, hb, -, -⟩ := par_fora_da_reta (m := m) hc (lt_of_le_of_lt h hε)
  refine ⟨_, h0, ?_⟩
  simp only [add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, zero_mul, one_mul, zero_add]
  exact hb.ne'

/-- **Empurrar sem quebrar as simetrias**: com `f` e `g` simétricas e `ε` real, `f − ε·g` é simétrica. -/
theorem empurrao_simetrico {f g : ℂ → ℂ} (hf : ClayRiemannProof.Analogs.Simetrica f)
    (hg : ClayRiemannProof.Analogs.Simetrica g) (ε : ℝ) :
    ClayRiemannProof.Analogs.Simetrica (fun w => f w - (ε : ℂ) * g w) := by
  refine ⟨fun w => by simp only [hf.1, hg.1], fun w => ?_⟩
  simp only [hf.2, hg.2, map_sub, map_mul, Complex.conj_ofReal]

/-- A constante `1` é simétrica: `ξ − ε` é um empurrão permitido. -/
theorem constante_simetrica : ClayRiemannProof.Analogs.Simetrica (fun _ => (1 : ℂ)) :=
  ⟨fun _ => rfl, fun _ => by simp⟩

/-- **A zeta empurrada**: os zeros de `ξ(½ + w) − ε·g(w)` (`g` simétrico, `ε` real) vêm em quartetos. -/
theorem zeta_empurrada_quarteto {g : ℂ → ℂ} (hg : ClayRiemannProof.Analogs.Simetrica g) (ε : ℝ) {w : ℂ}
    (h : ClayRiemannProof.Analogs.xiW w - (ε : ℂ) * g w = 0) :
    ClayRiemannProof.Analogs.xiW (-w) - (ε : ℂ) * g (-w) = 0 ∧
      ClayRiemannProof.Analogs.xiW (conj w) - (ε : ℂ) * g (conj w) = 0 ∧
      ClayRiemannProof.Analogs.xiW (-conj w) - (ε : ℂ) * g (-conj w) = 0 :=
  ClayRiemannProof.Analogs.quarteto_abstrato (f := fun w => ClayRiemannProof.Analogs.xiW w - (ε : ℂ) * g w)
    (empurrao_simetrico ClayRiemannProof.Analogs.xi_simetrica hg ε) h

end ClayRiemannProof.Forca
