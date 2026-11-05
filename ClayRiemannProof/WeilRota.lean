import ClayRiemannProof.Condicionais
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
# As pontes e as rotas do ataque de Weil (§60–61)

A forma de Weil `W` (a fórmula explícita com os primos e o fator `π·Γ`) ainda não pode ser definida no kernel: a
fórmula explícita não está na Mathlib. Por isso o ataque entra aqui como **estrutura com hipótese nomeada**
(`ProgramaDeWeil`): funções-teste com suporte em `[−L, L]`, crescentes em `L`; uma forma `W`; e o critério de Weil
(RH ⟺ `W ≥ 0` em toda escala) como campo. Tudo o que vem depois é provado no kernel a partir daí.

1. **Pontes da positividade.**
   - `positivo_desce`: valer numa escala dá todas as menores.
   - `rh_iff_sequencia`: basta uma sequência de escalas que vá ao infinito.
   - `nao_rh_iff`: a RH falsa é uma função-teste com `W < 0` numa escala finita.
   - `rh_iff_fronteira_ilimitada`: a RH é a fronteira (as escalas onde vale a positividade) não ter teto.
   - `Chuk2026`, `chuk_fronteira`: a positividade certificada em `L = 0,8` como hipótese nomeada; ela dá toda a
     fronteira até 0,8.
2. **A rota (A)+(B)** (`Aproximacao`): zeros de aproximações todos na reta (A) e todo zero de `ζ` limite deles (B).
   - `rh_de_aproximacao`: (A)+(B) dão a RH.
   - `rh_iff_existe_aproximacao`: a rota é **justa**; a RH vale ⟺ existe uma aproximação com (A) e (B).
   - `aproximacao_de_espectro`: a versão na variável `r` dos estados fundamentais (`ĝ(r) = 0`, `s = ½ + ir`), onde (A) é
     "todos os zeros de `ĝ` são reais".
3. **Hurwitz no kernel: a convergência dá (B) de graça.**
   - `hurwitz_passo`: se `F n → f` uniformemente num disco fechado, `f(ρ) = 0` e `f ≠ 0` na borda, então `F n` tem
     zero no disco para `n` grande. Prova pelo princípio do módulo máximo aplicado a `1/F n` (Mathlib), sem supor nada.
   - `rota_hurwitz`: (A) zeros dos `F n` só na reta + convergência localmente uniforme para um `f` que zera em cada
     zero de `ζ` sem ser identicamente nula perto dele ⟹ RH. (B) deixa de ser hipótese.
   - `zeta_nao_some_perto`: `ζ` não é identicamente nula perto de nenhum `ρ ≠ 1` (princípio da identidade, `ζ(2) ≠ 0`).
   - `rota_hurwitz_zeta`, `rh_iff_rota_hurwitz_zeta`: com `f = ζ` na faixa, a rota é justa: RH ⟺ existem aproximações
     holomorfas na faixa com zeros só na reta convergindo para `ζ`.
   - `rota_hurwitz_espectral`: a mesma rota na variável `r = −i(s − ½)` dos estados fundamentais de Weil: `G n`
     inteiras com zeros reais (A) convergindo localmente uniformemente para `g` com `g(r(ρ)) = 0` ⟹ RH.

Nada aqui prova RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.WeilRota

open Filter Topology Complex ClayRiemannProof.Zeta.Symmetry

/-! ## 1. O programa de Weil e as pontes da positividade -/

/-- **Um programa de Weil**: funções-teste com suporte em `[−L, L]` (crescentes em `L`), uma forma quadrática `W`, e o
critério de Weil como hipótese nomeada. -/
structure ProgramaDeWeil (F : Type*) where
  /-- As funções-teste com suporte em `[−L, L]`. -/
  teste : ℝ → Set F
  /-- Suporte maior admite mais funções-teste. -/
  mono : ∀ {L L' : ℝ}, L ≤ L' → teste L ⊆ teste L'
  /-- A forma de Weil. -/
  W : F → ℝ
  /-- O critério de Weil (hipótese nomeada): RH ⟺ `W ≥ 0` em toda escala. -/
  criterio : RiemannHypothesis ↔ ∀ L : ℝ, 0 < L → ∀ g ∈ teste L, 0 ≤ W g

namespace ProgramaDeWeil

variable {F : Type*} (P : ProgramaDeWeil F)

/-- Positividade na escala `L`. -/
def PositivoAte (L : ℝ) : Prop := ∀ g ∈ P.teste L, 0 ≤ P.W g

/-- **A positividade desce**: valer na escala `L'` dá todas as escalas menores. -/
theorem positivo_desce {L L' : ℝ} (h : L ≤ L') (hP : P.PositivoAte L') : P.PositivoAte L :=
  fun g hg => hP g (P.mono h hg)

/-- **A RH é a positividade em toda escala.** -/
theorem rh_iff : RiemannHypothesis ↔ ∀ L : ℝ, 0 < L → P.PositivoAte L := P.criterio

/-- **Basta uma sequência de escalas que vá ao infinito.** -/
theorem rh_iff_sequencia {Ls : ℕ → ℝ} (hL : Tendsto Ls atTop atTop) :
    RiemannHypothesis ↔ ∀ k, P.PositivoAte (Ls k) := by
  rw [P.rh_iff]
  constructor
  · intro h k
    exact P.positivo_desce (le_max_left (Ls k) 1) (h _ (lt_of_lt_of_le one_pos (le_max_right _ _)))
  · intro h L _
    obtain ⟨k, hk⟩ := (hL.eventually (eventually_ge_atTop L)).exists
    exact P.positivo_desce hk (h k)

/-- **A refutação é em escala finita**: a RH é falsa ⟺ existe `L > 0` e uma função-teste `g` de suporte `[−L, L]` com
`W(g) < 0`. -/
theorem nao_rh_iff : ¬ RiemannHypothesis ↔ ∃ L : ℝ, 0 < L ∧ ∃ g ∈ P.teste L, P.W g < 0 := by
  rw [P.criterio]
  simp only [not_forall, not_le, exists_prop]

/-- **A fronteira**: as escalas onde a positividade vale. -/
def Fronteira : Set ℝ := {L | P.PositivoAte L}

/-- A fronteira é um intervalo para baixo. -/
theorem fronteira_desce {L L' : ℝ} (h : L ≤ L') (hL' : L' ∈ P.Fronteira) : L ∈ P.Fronteira :=
  P.positivo_desce h hL'

/-- **A RH é a fronteira não ter teto.** -/
theorem rh_iff_fronteira_ilimitada : RiemannHypothesis ↔ ¬ BddAbove P.Fronteira := by
  rw [P.rh_iff]
  constructor
  · rintro h ⟨M, hM⟩
    have := hM (h (max M 0 + 1) (by positivity))
    linarith [le_max_left M 0]
  · intro h L _
    rw [not_bddAbove_iff] at h
    obtain ⟨L', hL', hlt⟩ := h L
    exact P.positivo_desce hlt.le hL'

/-- **Chuk (2026)**, como hipótese nomeada: a positividade certificada na escala `L = 0,8`. -/
def Chuk2026 : Prop := P.PositivoAte (4 / 5)

/-- **A fronteira certificada**: com Chuk (2026), toda escala até 0,8 está na fronteira. -/
theorem chuk_fronteira (h : P.Chuk2026) {L : ℝ} (hL : L ≤ 4 / 5) : L ∈ P.Fronteira :=
  P.positivo_desce hL h

end ProgramaDeWeil

/-! ## 2. A rota (A)+(B) -/

/-- **Uma aproximação**: os conjuntos de zeros das aproximações (por exemplo, dos estados fundamentais de Weil em escalas
crescentes), com (A) todos na reta e (B) todo zero de `ζ` limite deles. -/
structure Aproximacao where
  /-- Os zeros da `n`-ésima aproximação. -/
  zeros : ℕ → Set ℂ
  /-- (A): todos na reta. -/
  A : ∀ n, ∀ w ∈ zeros n, w.re = 1 / 2
  /-- (B): todo zero não trivial de `ζ` é limite de zeros das aproximações. -/
  B : ∀ ρ ∈ Z, ∃ w : ℕ → ℂ, (∀ n, w n ∈ zeros n) ∧ Tendsto w atTop (𝓝 ρ)

/-- **(A)+(B) dão a RH.** -/
theorem rh_de_aproximacao (ap : Aproximacao) : RiemannHypothesis :=
  TresEstados.forma_por_aproximacao ap.A ap.B

/-- **A rota é justa**: a RH vale ⟺ existe uma aproximação com (A) e (B). Com a RH, a família constante `Z` serve; o
conteúdo da rota está em achar a família certa sem supor a RH. -/
theorem rh_iff_existe_aproximacao : RiemannHypothesis ↔ Nonempty Aproximacao := by
  constructor
  · intro h
    exact ⟨⟨fun _ => Z, fun _ w hw => PorQueMeio.rh_iff_reta.mp h w hw,
      fun ρ hρ => ⟨fun _ => ρ, fun _ => hρ, tendsto_const_nhds⟩⟩⟩
  · rintro ⟨ap⟩
    exact rh_de_aproximacao ap

/-- O ponto da reta de altura `r`: `s = ½ + ir`. -/
noncomputable def naReta (r : ℂ) : ℂ := 1 / 2 + I * r

theorem naReta_re (r : ℂ) : (naReta r).re = 1 / 2 - r.im := by
  simp [naReta]
  ring

/-- **A rota na variável dos estados fundamentais**: se os zeros `r` de cada `ĝ` são todos reais (A) e todo zero de `ζ` é
limite de pontos `½ + ir_n` (B), há uma aproximação, e portanto a RH. -/
noncomputable def aproximacao_de_espectro (R : ℕ → Set ℂ) (hA : ∀ n, ∀ r ∈ R n, r.im = 0)
    (hB : ∀ ρ ∈ Z, ∃ r : ℕ → ℂ, (∀ n, r n ∈ R n) ∧ Tendsto (fun n => naReta (r n)) atTop (𝓝 ρ)) :
    Aproximacao where
  zeros n := naReta '' R n
  A := by
    rintro n w ⟨r, hr, rfl⟩
    rw [naReta_re, hA n r hr, sub_zero]
  B := by
    intro ρ hρ
    obtain ⟨r, hr, ht⟩ := hB ρ hρ
    exact ⟨fun n => naReta (r n), fun n => ⟨r n, hr n, rfl⟩, ht⟩

/-- **O resumo das rotas**: a RH é a fronteira de Weil sem teto (em qualquer programa de Weil), e é a existência de uma
aproximação com (A) e (B). -/
theorem rotas_do_ataque {F : Type*} (P : ProgramaDeWeil F) :
    (RiemannHypothesis ↔ ¬ BddAbove P.Fronteira) ∧ (RiemannHypothesis ↔ Nonempty Aproximacao) :=
  ⟨P.rh_iff_fronteira_ilimitada, rh_iff_existe_aproximacao⟩

/-! ## 3. Hurwitz: a convergência dá (B) de graça -/

open Metric in
/-- **O passo de Hurwitz** (princípio do módulo máximo aplicado a `1/F n`): se `F n → f` uniformemente no disco
fechado `B̄(ρ, r)`, `f(ρ) = 0` e `f` não se anula na borda, então, a partir de algum `n`, `F n` tem um zero no disco. -/
theorem hurwitz_passo {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {ρ : ℂ} {r : ℝ} (hr : 0 < r)
    (hF : ∀ n, DifferentiableOn ℂ (F n) (closedBall ρ r))
    (hconv : TendstoUniformlyOn F f atTop (closedBall ρ r))
    (hfc : ContinuousOn f (sphere ρ r)) (hf0 : f ρ = 0) (hfs : ∀ z ∈ sphere ρ r, f z ≠ 0) :
    ∀ᶠ n in atTop, ∃ w ∈ closedBall ρ r, F n w = 0 := by
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_sphere ρ r).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hr.le) hfc.norm
  have hm0 : 0 < ‖f z₀‖ := norm_pos_iff.mpr (hfs z₀ hz₀)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv (‖f z₀‖ / 2) (by positivity)] with n hn
  by_contra hne
  push Not at hne
  have hd : DiffContOnCl ℂ (fun z => (F n z)⁻¹) (ball ρ r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball ρ hr.ne']
    exact (hF n).inv hne
  have hC : ∀ z ∈ frontier (ball ρ r), ‖(fun z => (F n z)⁻¹) z‖ ≤ (‖f z₀‖ / 2)⁻¹ := by
    intro z hz
    rw [frontier_ball ρ hr.ne'] at hz
    have h1 : ‖f z₀‖ ≤ ‖f z‖ := isMinOn_iff.mp hmin z hz
    have h2 : dist (f z) (F n z) < ‖f z₀‖ / 2 := hn z (sphere_subset_closedBall hz)
    rw [dist_eq_norm] at h2
    have h3 : ‖f z₀‖ / 2 ≤ ‖F n z‖ := by
      have := norm_sub_norm_le (f z) (F n z)
      linarith
    simp only [norm_inv]
    exact inv_anti₀ (by positivity) h3
  have hρ := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd hC
    (subset_closure (mem_ball_self hr))
  have h4 : dist (f ρ) (F n ρ) < ‖f z₀‖ / 2 := hn ρ (mem_closedBall_self hr.le)
  rw [hf0, dist_zero_left] at h4
  simp only [norm_inv] at hρ
  have h5 : 0 < ‖F n ρ‖ := norm_pos_iff.mpr (hne ρ (mem_closedBall_self hr.le))
  have := (inv_le_inv₀ h5 (by positivity)).mp hρ
  linarith

/-- **A rota de Hurwitz**: (A) os `F n` só se anulam na reta (dentro de `U`), e `F n → f` localmente uniformemente num
aberto `U ⊇ Z`, com `f` zerando em cada zero não trivial de `ζ` sem ser identicamente nula perto dele. Então a RH vale.
A condição (B) da `Aproximacao` não é suposta: ela sai da convergência (`hurwitz_passo`). -/
theorem rota_hurwitz {U : Set ℂ} (hU : IsOpen U) (hZU : Z ⊆ U) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, DifferentiableOn ℂ (F n) U) (hA : ∀ n, ∀ w ∈ U, F n w = 0 → w.re = 1 / 2)
    (hconv : TendstoLocallyUniformlyOn F f atTop U)
    (hf : ∀ ρ ∈ Z, f ρ = 0 ∧ ¬ (∀ᶠ z in 𝓝 ρ, f z = 0)) : RiemannHypothesis := by
  have hfd : DifferentiableOn ℂ f U := hconv.differentiableOn (Eventually.of_forall hF) hU
  refine PorQueMeio.rh_iff_reta.mpr fun ρ hρ => ?_
  have hUρ : ∀ᶠ z in 𝓝 ρ, z ∈ U := hU.mem_nhds (hZU hρ)
  obtain ⟨hf0, hnz⟩ := hf ρ hρ
  have hiso : ∀ᶠ z in 𝓝[≠] ρ, f z ≠ 0 :=
    ((hfd.analyticAt hUρ).eventually_eq_zero_or_eventually_ne_zero).resolve_left hnz
  rw [eventually_nhdsWithin_iff] at hiso
  obtain ⟨r₀, hr₀, hball⟩ := Metric.eventually_nhds_iff.mp (hiso.and hUρ)
  have chave : ∀ r : ℝ, 0 < r → r < r₀ → |ρ.re - 1 / 2| ≤ r := by
    intro r hr hrr
    have hsub : Metric.closedBall ρ r ⊆ U := fun z hz =>
      (hball (lt_of_le_of_lt (Metric.mem_closedBall.mp hz) hrr)).2
    have hev := hurwitz_passo hr (fun n => (hF n).mono hsub)
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hconv _ hsub (isCompact_closedBall ρ r))
      (hfd.continuousOn.mono (Metric.sphere_subset_closedBall.trans hsub)) hf0
      (fun z hz => by
        have hd : dist z ρ = r := Metric.mem_sphere.mp hz
        refine (hball (by rw [hd]; exact hrr)).1 ?_
        intro h
        rw [h, dist_self] at hd
        exact hr.ne hd)
    obtain ⟨n, w, hw, hw0⟩ := hev.exists
    have hwre := hA n w (hsub hw) hw0
    have hdist : dist w ρ ≤ r := Metric.mem_closedBall.mp hw
    rw [dist_eq_norm] at hdist
    have := Complex.abs_re_le_norm (w - ρ)
    rw [Complex.sub_re, hwre] at this
    rw [abs_sub_comm]
    linarith
  by_contra hne
  have hd : 0 < |ρ.re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have h := chave (min (|ρ.re - 1 / 2| / 2) (r₀ / 2)) (by positivity)
    (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  have := min_le_left (|ρ.re - 1 / 2| / 2) (r₀ / 2)
  linarith

/-- **`ζ` não é identicamente nula perto de nenhum ponto `≠ 1`** (princípio da identidade em `ℂ ∖ {1}`, que é conexo,
com `ζ(2) ≠ 0`). -/
theorem zeta_nao_some_perto {ρ : ℂ} (hρ : ρ ≠ 1) : ¬ (∀ᶠ z in 𝓝 ρ, riemannZeta z = 0) := by
  intro h
  have hd : DifferentiableOn ℂ riemannZeta {1}ᶜ := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hA : AnalyticOnNhd ℂ riemannZeta {1}ᶜ := fun z hz =>
    hd.analyticAt (isOpen_compl_singleton.mem_nhds hz)
  have h0 := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    (show ρ ∈ ({1}ᶜ : Set ℂ) from hρ) h
  exact riemannZeta_ne_zero_of_one_lt_re (s := 2) (by norm_num)
    (h0 (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num))

/-- A faixa crítica aberta `0 < Re s < 1`. -/
def faixa : Set ℂ := {s | 0 < s.re ∧ s.re < 1}

theorem faixa_aberta : IsOpen faixa := by
  have h : IsOpen ({s : ℂ | (0 : ℝ) < s.re} ∩ {s : ℂ | s.re < 1}) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
  exact h

theorem Z_na_faixa : Z ⊆ faixa := fun _ hρ => hρ.2

theorem Z_ne_um {ρ : ℂ} (hρ : ρ ∈ Z) : ρ ≠ 1 := by
  intro h
  have := hρ.2.2
  rw [h, Complex.one_re] at this
  exact lt_irrefl _ this

/-- **A rota de Hurwitz com `ζ` como limite**: aproximações holomorfas na faixa com zeros só na reta, convergindo para
`ζ` localmente uniformemente na faixa, dão a RH. -/
theorem rota_hurwitz_zeta {F : ℕ → ℂ → ℂ} (hF : ∀ n, DifferentiableOn ℂ (F n) faixa)
    (hA : ∀ n, ∀ w ∈ faixa, F n w = 0 → w.re = 1 / 2)
    (hconv : TendstoLocallyUniformlyOn F riemannZeta atTop faixa) : RiemannHypothesis :=
  rota_hurwitz faixa_aberta Z_na_faixa hF hA hconv
    fun _ hρ => ⟨hρ.1, zeta_nao_some_perto (Z_ne_um hρ)⟩

/-- **A rota de Hurwitz é justa**: a RH vale ⟺ existem aproximações holomorfas na faixa, com zeros só na reta,
convergindo para `ζ` localmente uniformemente na faixa. (Com a RH, a sequência constante `ζ` serve; o conteúdo está em
achar aproximações que não suponham a RH, como os estados fundamentais de Weil.) -/
theorem rh_iff_rota_hurwitz_zeta : RiemannHypothesis ↔ ∃ F : ℕ → ℂ → ℂ,
    (∀ n, DifferentiableOn ℂ (F n) faixa) ∧ (∀ n, ∀ w ∈ faixa, F n w = 0 → w.re = 1 / 2) ∧
      TendstoLocallyUniformlyOn F riemannZeta atTop faixa := by
  constructor
  · intro h
    refine ⟨fun _ => riemannZeta, fun _ z hz => ?_, fun _ w hw hw0 => PorQueMeio.rh_iff_reta.mp h w ⟨hw0, hw⟩, ?_⟩
    · refine (differentiableAt_riemannZeta ?_).differentiableWithinAt
      intro h1
      have := hz.2
      rw [h1, Complex.one_re] at this
      exact lt_irrefl _ this
    · exact (Metric.tendstoUniformlyOn_iff.mpr fun ε hε =>
        Eventually.of_forall fun _ _ _ => by simpa using hε).tendstoLocallyUniformlyOn
  · rintro ⟨F, hF, hA, hconv⟩
    exact rota_hurwitz_zeta hF hA hconv

/-- A altura `r = −i(s − ½)`, de modo que `s = ½ + ir`; `r` é real exatamente na reta. -/
noncomputable def altura (s : ℂ) : ℂ := -I * (s - 1 / 2)

theorem altura_im (s : ℂ) : (altura s).im = 1 / 2 - s.re := by
  simp [altura]

theorem altura_diff : Differentiable ℂ altura := by
  unfold altura
  fun_prop

/-- **A rota de Hurwitz na variável espectral** (a dos estados fundamentais de Weil, `ĝ*(r)`): se cada `G n` é inteira
com **todos os zeros reais** (A), e `G n → g` localmente uniformemente, com `g` zerando na altura de cada zero não
trivial de `ζ` sem ser identicamente nula perto dele, então a RH vale. -/
theorem rota_hurwitz_espectral {G : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hG : ∀ n, Differentiable ℂ (G n))
    (hA : ∀ n r, G n r = 0 → r.im = 0) (hconv : TendstoLocallyUniformly G g atTop)
    (hg : ∀ ρ ∈ Z, g (altura ρ) = 0 ∧ ¬ (∀ᶠ z in 𝓝 ρ, g (altura z) = 0)) : RiemannHypothesis := by
  refine rota_hurwitz (U := Set.univ) (F := fun n => G n ∘ altura) (f := g ∘ altura) isOpen_univ
    (Set.subset_univ _) (fun n => ((hG n).comp altura_diff).differentiableOn) (fun n w _ hw => ?_) ?_ hg
  · have := hA n _ hw
    rw [altura_im] at this
    linarith
  · exact (tendstoLocallyUniformlyOn_univ.mpr hconv).comp altura (Set.mapsTo_univ _ _)
      altura_diff.continuous.continuousOn

end ClayRiemannProof.WeilRota
