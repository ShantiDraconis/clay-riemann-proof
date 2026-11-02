import ClayRiemannProof.BaezDuarteGap
import ClayRiemannProof.HyperTruncation
import ClayRiemannProof.Bicomplex
import ClayRiemannProof.Locks
import ClayRiemannProof.QuasiRH
import ClayRiemannProof.HeightThirteen
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Pontes, nós, leis, operadores, vetores e tensões

Este arquivo junta, no kernel, todas as formulações do problema que o repositório contém, e acrescenta a camada
de operadores, vetores e tensões sobre os zeros.

* **Vetor de desvio** `δ(s) = (Re s − ½, Im s)`: a primeira coordenada é a **tensão** `b`, a segunda é a altura
  `t`. Os três operadores de Klein (`tensao`, `espelho`, `torcao`, de `Zeta.Symmetry`) viram trocas de sinal
  `(−b, −t)`, `(b, −t)`, `(−b, t)`, e a compressão vira multiplicação por escalar (`delta_*`).
* **Leis incondicionais**: todo quarteto tem baricentro no neutro `½` (`baricentro`) e as tensões dele se cancelam
  (`tensoes_cancelam`). A **energia** do quarteto, a soma dos quadrados das tensões, é `4b²` (`energia_eq`), e para todo
  zero não trivial ela é `< 1` (`energia_lt_um`). O vetor de todo zero não trivial mora em
  `(−½, ½) × {|t| > 13}` (`vetor_de_zero`, que usa `HeightThirteen`).
* **O nó**: a órbita de Klein de um zero (`orbita`) tem 2 pontos na reta e 4 fora dela (`card_orbita_reta`,
  `card_orbita_fora`). Clay ⟺ todo nó se desfaz num par (`target_iff_nos_desfeitos`); RH falsa ⟺ existe um nó
  de 4 pontos (`not_target_iff_no`).
* **Parâmetro espectral** `λ(s) = s(1 − s)`, a normalização de Selberg, em que `λ = ¼ + t²` na reta:
  `Im λ = −2bt` (`lam_im`), e Clay ⟺ todo `λ(ρ)` é real (`target_iff_lam_real`). Incondicionalmente,
  `Re λ(ρ) > 169` para todo zero não trivial (`lam_re_gt`).
* **Operador (Hilbert–Pólya, só a ponte)**: com `γ(s) = −i(s − ½)`, se algum operador simétrico `T` num espaço com
  produto interno complexo tiver todo `γ(ρ)` como autovalor, vale o enunciado do Clay (`hilbert_polya`). Nenhum tal
  `T` é conhecido; construí-lo a partir da aritmética é o problema.
* **A ponte única** (`pontes`): treze formulações provadas equivalentes num só `List.TFAE`. Entram nele o Clay,
  Báez-Duarte, o corte em `ω`, os mundos finitos, o bicomplexo, o desvio `b = 0`, o semiplano direito, o fim fechado,
  a torção, a energia, os nós, `λ` real e `γ` real.

**O que isto não é**: a ponte única mostra que as treze formulações são **a mesma proposição**; nenhuma é mais
fraca que as outras, e provar qualquer uma é provar RH. Nada aqui prova RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Bridges

open Complex ComplexConjugate ClayRiemannProof.Zeta.Symmetry

/-! ## 1. O vetor de desvio -/

/-- **Vetor de desvio**: `δ(s) = (Re s − ½, Im s)`. A primeira coordenada é a tensão `b`, a segunda a altura `t`. -/
noncomputable def delta (s : ℂ) : ℝ × ℝ := (s.re - 1 / 2, s.im)

/-- `δ` é injetiva: é uma carta de `ℂ` centrada no neutro. -/
theorem delta_injective : Function.Injective delta := by
  intro s w h
  simp only [delta, Prod.mk.injEq] at h
  apply Complex.ext <;> linarith [h.1, h.2]

/-- O único ponto de vetor nulo é o neutro `½`. -/
theorem delta_eq_zero_iff (s : ℂ) : delta s = 0 ↔ s = 1 / 2 := by
  rw [Prod.ext_iff]
  simp only [delta, Prod.fst_zero, Prod.snd_zero]
  constructor
  · rintro ⟨h1, h2⟩
    apply Complex.ext
    · simp; linarith
    · simpa using h2
  · rintro rfl
    norm_num

/-- A **tensão** `s ↦ 1 − s` age como `(b, t) ↦ (−b, −t)`. -/
theorem delta_tensao (s : ℂ) : delta (tensao s) = -delta s := by
  unfold delta tensao
  ext
  · simp; ring
  · simp

/-- O **espelho** `s ↦ s̄` age como `(b, t) ↦ (b, −t)`. -/
theorem delta_espelho (s : ℂ) : delta (espelho s) = ((delta s).1, -(delta s).2) := by
  unfold delta espelho
  ext <;> simp

/-- A **torção** `s ↦ 1 − s̄` age como `(b, t) ↦ (−b, t)`. -/
theorem delta_torcao (s : ℂ) : delta (torcao s) = (-(delta s).1, (delta s).2) := by
  unfold delta torcao
  ext
  · simp; ring
  · simp

/-- A **compressão** de fator `l` age como multiplicação do vetor por `l`. -/
theorem delta_compressao (l : ℝ) (s : ℂ) : delta (compressao l s) = l • delta s := by
  unfold delta compressao
  ext <;> simp

/-! ## 2. Leis do quarteto -/

/-- **Lei do baricentro**: o centro de massa de todo quarteto `s, s̄, 1 − s, 1 − s̄` é o neutro `½`. -/
theorem baricentro (s : ℂ) : (s + espelho s + tensao s + torcao s) / 4 = 1 / 2 := by
  unfold espelho tensao torcao
  ring

/-- **As tensões do quarteto se cancelam**: `b + b − b − b = 0`. -/
theorem tensoes_cancelam (s : ℂ) :
    (delta s).1 + (delta (espelho s)).1 + (delta (tensao s)).1 + (delta (torcao s)).1 = 0 := by
  simp only [delta_espelho, delta_tensao, delta_torcao, Prod.fst_neg]
  ring

/-- **Energia do quarteto**: a soma dos quadrados das quatro tensões. -/
noncomputable def energia (s : ℂ) : ℝ :=
  (delta s).1 ^ 2 + (delta (espelho s)).1 ^ 2 + (delta (tensao s)).1 ^ 2 + (delta (torcao s)).1 ^ 2

theorem energia_eq (s : ℂ) : energia s = 4 * (s.re - 1 / 2) ^ 2 := by
  unfold energia
  simp only [delta_espelho, delta_tensao, delta_torcao, Prod.fst_neg]
  simp only [delta]
  ring

theorem energia_eq_zero_iff (s : ℂ) : energia s = 0 ↔ s.re = 1 / 2 := by
  rw [energia_eq]
  constructor
  · intro h
    have h2 : (s.re - 1 / 2) ^ 2 = 0 := by linarith
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    linarith
  · intro h
    rw [h]
    ring

/-- **Incondicional**: a energia de todo zero não trivial é menor que `1` (colar `|b| < ½`). -/
theorem energia_lt_um {s : ℂ} (hs : s ∈ Z) : energia s < 1 := by
  rw [energia_eq]
  have h := abs_lt.mp (colar_meio s hs)
  nlinarith [h.1, h.2]

/-- **Incondicional**: o vetor de todo zero não trivial mora em `(−½, ½) × {|t| > 13}`. -/
theorem vetor_de_zero {s : ℂ} (hs : s ∈ Z) : |(delta s).1| < 1 / 2 ∧ 13 < |(delta s).2| := by
  refine ⟨colar_meio s hs, ?_⟩
  by_contra h
  exact ClayRiemannProof.HeightThirteen.faixa_sem_zeros hs.2.1 hs.2.2 (not_lt.mp h) hs.1

/-! ## 3. O nó e a sua dissolução -/

open Classical in
/-- **O nó**: a órbita de Klein de `s`, como conjunto finito. -/
noncomputable def orbita (s : ℂ) : Finset ℂ := {s, espelho s, tensao s, torcao s}

/-- Na reta, o nó se desfaz num par `{s, s̄}`. -/
theorem card_orbita_reta {s : ℂ} (hs : s ∈ Z) (h : s.re = 1 / 2) : (orbita s).card = 2 := by
  classical
  have ht : torcao s = s := (torcao_fixo_iff s).mpr h
  have hte : tensao s = espelho s := by
    apply Complex.ext
    · simp [tensao, espelho]; linarith
    · simp [tensao, espelho]
  have hne : espelho s ≠ s := (quarteto hs).1
  have e : orbita s = {s, espelho s} := by
    unfold orbita
    rw [ht, hte]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [e, Finset.card_pair hne.symm]

/-- Fora da reta, o nó tem quatro pontos distintos. -/
theorem card_orbita_fora {s : ℂ} (hs : s ∈ Z) (h : s.re ≠ 1 / 2) : (orbita s).card = 4 := by
  classical
  obtain ⟨he, ht, -, hq⟩ := quarteto hs
  obtain ⟨hr, het, her, htr⟩ := hq h
  have h1 : s ∉ ({espelho s, tensao s, torcao s} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨he.symm, ht.symm, hr.symm⟩
  have h2 : espelho s ∉ ({tensao s, torcao s} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨het, her⟩
  unfold orbita
  rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_pair htr]

/-- **Clay ⟺ todo nó se desfaz**: todo quarteto de zero não trivial degenera num par. -/
theorem target_iff_nos_desfeitos : Target ↔ ∀ s ∈ Z, (orbita s).card = 2 := by
  constructor
  · intro hT s hs
    exact card_orbita_reta hs (riemann_imp_re hT hs)
  · intro h
    refine riemann_iff_torcao.mpr fun s hs => (torcao_fixo_iff s).mpr ?_
    by_contra hne
    have h4 := card_orbita_fora hs hne
    rw [h s hs] at h4
    norm_num at h4

/-- **RH falsa ⟺ existe um nó de quatro pontos.** -/
theorem not_target_iff_no : ¬ Target ↔ ∃ s ∈ Z, (orbita s).card = 4 := by
  rw [target_iff_nos_desfeitos]
  constructor
  · intro h
    simp only [not_forall] at h
    obtain ⟨s, hs, hc⟩ := h
    refine ⟨s, hs, ?_⟩
    by_cases hre : s.re = 1 / 2
    · exact absurd (card_orbita_reta hs hre) hc
    · exact card_orbita_fora hs hre
  · rintro ⟨s, hs, hc⟩ h
    rw [h s hs] at hc
    norm_num at hc

/-! ## 4. O parâmetro espectral `λ = s(1 − s)` -/

/-- **Parâmetro espectral** `λ(s) = s(1 − s)` (normalização de Selberg). -/
def lam (s : ℂ) : ℂ := s * (1 - s)

/-- `λ` não vê a tensão: `λ(1 − s) = λ(s)`. -/
theorem lam_tensao (s : ℂ) : lam (tensao s) = lam s := by
  unfold lam tensao
  ring

/-- O espelho conjuga `λ`. -/
theorem lam_espelho (s : ℂ) : lam (espelho s) = conj (lam s) := by
  unfold lam espelho
  simp [map_mul, map_sub, map_one]

theorem lam_re (s : ℂ) : (lam s).re = 1 / 4 - (s.re - 1 / 2) ^ 2 + s.im ^ 2 := by
  unfold lam
  simp
  ring

/-- `Im λ = −2bt`: a parte imaginária de `λ` é o produto da tensão pela altura. -/
theorem lam_im (s : ℂ) : (lam s).im = -2 * (s.re - 1 / 2) * s.im := by
  unfold lam
  simp
  ring

/-- Na reta, `λ = ¼ + t²`. -/
theorem lam_na_reta {s : ℂ} (h : s.re = 1 / 2) : lam s = ((1 / 4 + s.im ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [lam_re, h, Complex.ofReal_re]; ring
  · rw [lam_im, h, Complex.ofReal_im]; ring

/-- **Clay ⟺ todo parâmetro espectral `λ(ρ)` é real.** -/
theorem target_iff_lam_real : Target ↔ ∀ s ∈ Z, (lam s).im = 0 := by
  constructor
  · intro hT s hs
    rw [lam_im, riemann_imp_re hT hs]
    ring
  · intro h
    refine riemann_iff_torcao.mpr fun s hs => (torcao_fixo_iff s).mpr ?_
    have h1 := h s hs
    rw [lam_im] at h1
    have h2 : (s.re - 1 / 2) * s.im = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · exact absurd h3 (im_ne_zero_of_mem_Z hs)

/-- **Incondicional**: `Re λ(ρ) > 169` para todo zero não trivial (`|b| < ½` e `|t| > 13`). -/
theorem lam_re_gt {s : ℂ} (hs : s ∈ Z) : 169 < (lam s).re := by
  rw [lam_re]
  obtain ⟨h1, h2⟩ := vetor_de_zero hs
  have hb : |s.re - 1 / 2| < 1 / 2 := h1
  have ht : 13 < |s.im| := h2
  have hb2 := abs_lt.mp hb
  have ht2 : (169 : ℝ) < s.im ^ 2 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg s.im]
  nlinarith [hb2.1, hb2.2]

/-! ## 5. O operador: a ponte de Hilbert–Pólya -/

/-- **Ordenada complexa** `γ(s) = −i(s − ½)`: `Re γ = t` e `Im γ = −b`. -/
noncomputable def gam (s : ℂ) : ℂ := -I * (s - 1 / 2)

theorem gam_re (s : ℂ) : (gam s).re = s.im := by
  unfold gam
  simp

theorem gam_im (s : ℂ) : (gam s).im = -(s.re - 1 / 2) := by
  unfold gam
  simp

/-- **Clay ⟺ toda ordenada `γ(ρ)` é real.** -/
theorem target_iff_gam_real : Target ↔ ∀ s ∈ Z, (gam s).im = 0 := by
  constructor
  · intro hT s hs
    rw [gam_im, riemann_imp_re hT hs]
    ring
  · intro h
    refine riemann_iff_torcao.mpr fun s hs => (torcao_fixo_iff s).mpr ?_
    have h1 := h s hs
    rw [gam_im] at h1
    linarith

/-- **Ponte de Hilbert–Pólya (só a ponte)**: se um operador simétrico `T` num espaço com produto interno complexo
tiver todo `γ(ρ)` como autovalor, vale o enunciado do Clay. Os autovalores de `T` são reais
(`LinearMap.IsSymmetric.conj_eigenvalue_eq_self`). Nenhum tal `T` é conhecido. -/
theorem hilbert_polya {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (h : ∀ s ∈ Z, Module.End.HasEigenvalue T (gam s)) : Target :=
  target_iff_gam_real.mpr fun s hs => Complex.conj_eq_iff_im.mp (hT.conj_eigenvalue_eq_self (h s hs))

/-! ## 6. A ponte única -/

/-- **A ponte única**: as treze formulações do repositório são a mesma proposição.

1. o enunciado do Clay; 2. Báez-Duarte, `⨅ D_N = 0`; 3. `D_ω` infinitesimal no hipernatural `ω`;
4. RH em todo mundo finito `Sat M`; 5. RH bicomplexa; 6. desvio `b = 0`; 7. sem zeros em `½ < Re s < 1`;
8. todo fim fechado `[a, ∞)`, `a > ½`, livre de zeros; 9. todo zero fixo pela torção; 10. energia zero;
11. todo nó desfeito; 12. `λ(ρ)` real; 13. `γ(ρ)` real. -/
theorem pontes : List.TFAE
    [ Target,
      Gap,
      HyperTruncation.IsInfinitesimal HyperTruncation.DOmega,
      ∀ M : ℕ, FiniteWorlds.RHnoMundo M,
      Bicomplex.RHbc,
      ∀ ρ : ℂ, riemannZeta ρ = 0 → (¬ ∃ n : ℕ, ρ = -2 * (n + 1)) → ρ ≠ 1 → ρ.re - 1 / 2 = 0,
      NoZero_right_half,
      ∀ a : ℝ, 1 / 2 < a → FimLivre a,
      ∀ s ∈ Z, torcao s = s,
      ∀ s ∈ Z, energia s = 0,
      ∀ s ∈ Z, (orbita s).card = 2,
      ∀ s ∈ Z, (lam s).im = 0,
      ∀ s ∈ Z, (gam s).im = 0 ] := by
  tfae_have 1 ↔ 2 := target_iff_gap
  tfae_have 1 ↔ 3 := HyperTruncation.target_iff_DOmega_infinitesimal
  tfae_have 1 ↔ 4 := FiniteWorlds.target_iff_todos_os_mundos
  tfae_have 1 ↔ 5 := Bicomplex.target_iff_RHbc
  tfae_have 1 ↔ 6 := Locks.target_iff_desvio_zero
  tfae_have 1 ↔ 7 := target_iff_noZero_right_half
  tfae_have 1 ↔ 8 := riemann_iff_fim
  tfae_have 1 ↔ 9 := riemann_iff_torcao
  tfae_have 1 ↔ 10 := riemann_iff_torcao.trans
    (forall₂_congr fun s _ => (torcao_fixo_iff s).trans (energia_eq_zero_iff s).symm)
  tfae_have 1 ↔ 11 := target_iff_nos_desfeitos
  tfae_have 1 ↔ 12 := target_iff_lam_real
  tfae_have 1 ↔ 13 := target_iff_gam_real
  tfae_finish

end ClayRiemannProof.Bridges
