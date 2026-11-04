import ClayRiemannProof.Geometrias

/-!
# A máquina de teste da RH, o terceiro estado, e as pontes da RH com os outros problemas

1. **A RH reduzida a uma máquina** (`mmc`, `delta`, `harm`, `Lag`, `teste`, `maquina`, `maquina_iff`, `LagariasPi1`,
   `rh_iff_maquina_nunca_para`, `refutacao_finita`, `rh_pi1`, `lag_ate_6`, `maquina_6`). Pelo critério de Lagarias na
   forma usada por Yedidia–Aaronson (2016),

       RH  ⟺  ∀ n ≥ 1,  (H_{δ(n)} − n²/2)² < 36 n³,    δ(n) = ∏_{m<n} lcm(1, …, m),

   onde `H_N = Σ_{k≤N} 1/k` (`∏_{j≤m} η(j) = lcm(1, …, m)`). Cada `n` é uma conta finita em `ℚ`; a máquina testa
   `n = 1, 2, …` e para exatamente quando acha uma violação. Com o enunciado nomeado `LagariasPi1`: **RH ⟺ a máquina
   nunca para**; **RH falsa ⟺ ela para num `N` finito**, e a parada é um certificado que o kernel confere por conta.
   O kernel rodou a máquina até `n = 6` (`δ(6) = 8 640`); `computations/maquina/maquina_rh.py` a roda em ponto
   flutuante até `n = 10⁷` (README §43).
2. **O terceiro estado.** Na análise ele é `κ = 0` (`Q_kappa_zero`): o zero duplo sobre a reta, a fronteira entre os dois
   zeros na reta (`κ > 0`) e o quarteto fora (`κ < 0`). Na lógica, a RH é Π₁ (`rh_pi1`): se for falsa, a máquina para e
   a parada é demonstrável. Logo "nem demonstrável nem refutável" (independente de ZFC) implicaria RH verdadeira.
   O terceiro estado da RH colapsa no "verdadeira". Isso é um metateorema (precisa de um predicado de
   demonstrabilidade), comentado aqui, não formalizado.
3. **A ponte com P vs NP** é só a do nível lógico: P ≠ NP é Π₂ (para toda máquina e todo polinômio existe uma entrada
   em que ela falha), e para Π₂ a independência **não** colapsa. Não há redução conhecida entre RH e P vs NP em
   nenhum sentido. A ponte provada com a complexidade é outra: com a RH generalizada, o teste de Miller é um algoritmo
   determinístico polinomial para primalidade (Miller 1976, Bach 1990); AKS (2002) tirou a hipótese.
4. **A ponte com Hodge: positividade ⟺ RH** (`positividade_iff`, `ponte_hodge`, `positividade_iff_hasse`,
   `positividade_F13`). A forma `m² − λmn + qn²` é `≥ 0` para todo `m, n` exatamente quando `λ² ≤ 4q`, que é a RH do
   fator `1 − λu + qu²`. Para uma curva, `m² − a mn + qn² = deg(m − nφ)` (φ = Frobenius) é um grau, logo `≥ 0`: é
   assim que Weil prova a RH das curvas (positividade de Castelnuovo–Severi, o índice de Hodge). Para ζ, o análogo é
   o critério de positividade de Weil, equivalente à RH e aberto.
5. **A ponte com BSD** (`hasse_E0_97`, `hasse_E1_97`, `E0_supersingular_97`). Os fatores locais de `L(E, s)` satisfazem
   a RH local (`a_p² ≤ 4p`); o kernel confere para `E₀: y² = x³ − x` e `E₁: y² = x³ − 2` em todo primo `5 ≤ p ≤ 97`, e
   que `a_p(E₀) = 0` para `p ≡ 3 (mod 4)` (multiplicação complexa). O produto parcial `Π N_p/p` de Birch e
   Swinnerton-Dyer está em `computations/maquina/bsd_produto.py`.
6. **Yang–Mills (gap espectral)**: nos análogos, RH ⟺ gap (`Geometrias.selberg_reta`: `λ₁ ≥ ¼`;
   `Geometrias.Ramanujan`: `λ² ≤ 4q`). É analogia de forma, não implicação. **Navier–Stokes**: nenhuma ponte conhecida.

Os enunciados nomeados são teoremas publicados (`Prop`), nunca `axiom`. Nada aqui prova ou refuta RH, P vs NP, BSD,
Hodge ou Yang–Mills. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Maquina

open Complex

/-! ## 1. A máquina de teste -/

/-- `lcm(1, …, m)`. -/
def mmc (m : ℕ) : ℕ := (List.range m).foldl (fun a j => Nat.lcm a (j + 1)) 1

/-- `δ(n) = ∏_{m<n} lcm(1, …, m)`. -/
def delta (n : ℕ) : ℕ := (List.range n).foldl (fun a m => a * mmc m) 1

/-- `H_N = A_N/B_N` em inteiros: `A_{k+1} = A_k(k + 1) + B_k`, `B_{k+1} = B_k(k + 1)` (`B_N = N!`). -/
def hpar : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | k + 1 => ((hpar k).1 * (k + 1) + (hpar k).2, (hpar k).2 * (k + 1))

/-- `H_N` em `ℚ`. -/
def harm (N : ℕ) : ℚ := ((hpar N).1 : ℚ) / (hpar N).2

theorem hpar_den_pos (N : ℕ) : 0 < (hpar N).2 := by
  induction N with
  | zero => simp [hpar]
  | succ k ih => simp only [hpar]; positivity

/-- **`H_N` é a soma harmônica**: `H_N = Σ_{k<N} 1/(k + 1)`. -/
theorem harm_eq_sum (N : ℕ) : harm N = ∑ k ∈ Finset.range N, 1 / ((k : ℚ) + 1) := by
  induction N with
  | zero => simp [harm, hpar]
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih]
    have hB : ((hpar k).2 : ℚ) ≠ 0 := by exact_mod_cast (hpar_den_pos k).ne'
    simp only [harm, hpar]
    push_cast
    field_simp

/-- **A desigualdade de Lagarias no passo `n`**, em inteiros: `(2A − n²B)² < 144 n³ B²` com `H_{δ(n)} = A/B`. -/
def Lag (n : ℕ) : Prop :=
  (2 * ((hpar (delta n)).1 : ℤ) - (n : ℤ) ^ 2 * (hpar (delta n)).2) ^ 2 < 144 * (n : ℤ) ^ 3 * ((hpar (delta n)).2 : ℤ) ^ 2

instance (n : ℕ) : Decidable (Lag n) := by
  unfold Lag
  infer_instance

/-- **`Lag n` é a desigualdade de Lagarias**: `(H_{δ(n)} − n²/2)² < 36 n³`. -/
theorem lag_iff (n : ℕ) : Lag n ↔ (harm (delta n) - (n : ℚ) ^ 2 / 2) ^ 2 < 36 * (n : ℚ) ^ 3 := by
  have hB : (0 : ℚ) < (hpar (delta n)).2 := by exact_mod_cast hpar_den_pos (delta n)
  have key : (harm (delta n) - (n : ℚ) ^ 2 / 2) ^ 2 =
      (2 * ((hpar (delta n)).1 : ℚ) - (n : ℚ) ^ 2 * (hpar (delta n)).2) ^ 2 / (4 * ((hpar (delta n)).2 : ℚ) ^ 2) := by
    unfold harm
    field_simp
    ring
  rw [key, div_lt_iff₀ (by positivity)]
  unfold Lag
  constructor
  · intro h
    have h' : ((2 * ((hpar (delta n)).1 : ℤ) - (n : ℤ) ^ 2 * (hpar (delta n)).2) ^ 2 : ℚ) <
        ((144 * (n : ℤ) ^ 3 * ((hpar (delta n)).2 : ℤ) ^ 2 : ℤ) : ℚ) := by exact_mod_cast h
    push_cast at h'
    linarith
  · intro h
    have h' : ((2 * ((hpar (delta n)).1 : ℤ) - (n : ℤ) ^ 2 * (hpar (delta n)).2) ^ 2 : ℚ) <
        ((144 * (n : ℤ) ^ 3 * ((hpar (delta n)).2 : ℤ) ^ 2 : ℤ) : ℚ) := by
      push_cast
      linarith
    exact_mod_cast h'

/-- Um passo da máquina. -/
def teste (n : ℕ) : Bool := decide (Lag n)

/-- **A máquina**: testa `n = 1, …, N` e devolve `true` (para) se achar uma violação. -/
def maquina (N : ℕ) : Bool := (List.range N).any fun k => !teste (k + 1)

/-- **A máquina para em `N` ⟺ há violação em `1 ≤ n ≤ N`.** -/
theorem maquina_iff (N : ℕ) : maquina N = true ↔ ∃ n, 1 ≤ n ∧ n ≤ N ∧ ¬ Lag n := by
  unfold maquina teste
  simp only [List.any_eq_true, List.mem_range, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not]
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨k + 1, by omega, by omega, h⟩
  · rintro ⟨n, h1, h2, h⟩
    refine ⟨n - 1, by omega, ?_⟩
    rwa [Nat.sub_add_cancel h1]

/-- **Lagarias, forma Π₁** (via Yedidia–Aaronson 2016) — enunciado nomeado: RH ⟺
`∀ n ≥ 1, (H_{δ(n)} − n²/2)² < 36 n³`. -/
def LagariasPi1 : Prop :=
  RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → (harm (delta n) - (n : ℚ) ^ 2 / 2) ^ 2 < 36 * (n : ℚ) ^ 3

theorem rh_iff_lag (h : LagariasPi1) : RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → Lag n := by
  have h' : RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → (harm (delta n) - (n : ℚ) ^ 2 / 2) ^ 2 < 36 * (n : ℚ) ^ 3 := h
  rw [h']
  exact forall_congr' fun n => imp_congr_right fun _ => (lag_iff n).symm

/-- **RH ⟺ a máquina nunca para.** -/
theorem rh_iff_maquina_nunca_para (h : LagariasPi1) : RiemannHypothesis ↔ ∀ N, maquina N = false := by
  rw [rh_iff_lag h]
  constructor
  · intro hL N
    cases hm : maquina N
    · rfl
    · obtain ⟨n, h1, -, hn⟩ := (maquina_iff N).mp hm
      exact absurd (hL n h1) hn
  · intro hM n hn
    by_contra hc
    have h2 := (maquina_iff n).mpr ⟨n, hn, le_rfl, hc⟩
    rw [hM n] at h2
    exact Bool.false_ne_true h2

/-- **A refutação é finita**: RH falsa ⟺ a máquina para em algum `N`. -/
theorem refutacao_finita (h : LagariasPi1) : ¬ RiemannHypothesis ↔ ∃ N, maquina N = true := by
  rw [rh_iff_maquina_nunca_para h, not_forall]
  simp only [Bool.not_eq_false]

/-- **A RH é Π₁**: equivale a `∀ n, φ n = true` para uma função `φ : ℕ → Bool` que o kernel calcula. -/
theorem rh_pi1 (h : LagariasPi1) : ∃ φ : ℕ → Bool, RiemannHypothesis ↔ ∀ n, φ n = true := by
  refine ⟨fun n => teste (n + 1), ?_⟩
  rw [rh_iff_lag h]
  constructor
  · intro hL n
    exact decide_eq_true (hL (n + 1) (by omega))
  · intro hφ n hn
    have h1 : teste (n - 1 + 1) = true := hφ (n - 1)
    rw [Nat.sub_add_cancel hn] at h1
    exact of_decide_eq_true h1

/-- **O kernel rodou a máquina**: `Lag 1, …, Lag 6` valem (`δ(6) = 8 640`). -/
theorem lag_ate_6 : Lag 1 ∧ Lag 2 ∧ Lag 3 ∧ Lag 4 ∧ Lag 5 ∧ Lag 6 := by
  decide +kernel

/-- **A máquina não para até `N = 6`.** -/
theorem maquina_6 : maquina 6 = false := by
  decide +kernel

/-- Os valores de `δ`: `1, 1, 2, 12, 144, 8 640, 518 400`. -/
theorem delta_valores :
    delta 1 = 1 ∧ delta 2 = 1 ∧ delta 3 = 2 ∧ delta 4 = 12 ∧ delta 5 = 144 ∧ delta 6 = 8640 ∧ delta 7 = 518400 := by
  decide +kernel

/-! ## 2. O terceiro estado na análise: `κ = 0` -/

/-- **`κ = 0` é o zero duplo sobre a reta**: `Q(w) = (w − iγ₀)²(w + iγ₀)²`. -/
theorem Q_kappa_zero (γ₀ : ℝ) (w : ℂ) :
    QuartetoForcado.Q γ₀ 0 w = (w - I * γ₀) ^ 2 * (w + I * γ₀) ^ 2 := by
  unfold QuartetoForcado.Q
  push_cast
  ring

/-! ## 4. A ponte com Hodge: positividade ⟺ RH -/

/-- **Positividade ⟺ discriminante**: `m² − λmn + qn² ≥ 0` para todos `m, n` reais ⟺ `λ² ≤ 4q` (`q > 0`). -/
theorem positividade_iff {l q : ℝ} (hq : 0 < q) :
    (∀ m n : ℝ, 0 ≤ m ^ 2 - l * m * n + q * n ^ 2) ↔ l ^ 2 ≤ 4 * q := by
  constructor
  · intro h
    have := h l 2
    nlinarith
  · intro h m n
    nlinarith [sq_nonneg (2 * q * n - l * m), mul_nonneg (sub_nonneg.mpr h) (sq_nonneg m)]

/-- **A ponte com Hodge**: positividade da forma ⟺ os zeros de `1 − λu + qu²` no círculo `|u|² = 1/q` (a RH). -/
theorem ponte_hodge {l q : ℝ} (hq : 0 < q) :
    (∀ m n : ℝ, 0 ≤ m ^ 2 - l * m * n + q * n ^ 2) ↔
      ∀ u : ℂ, 1 - (l : ℂ) * u + (q : ℂ) * u ^ 2 = 0 → normSq u = 1 / q :=
  (positividade_iff hq).trans (Geometrias.circulo_iff hq).symm

/-- **Versão inteira** (a do grau `deg(m − nφ)`): `m² − amn + qn² ≥ 0` para `m, n ∈ ℤ` ⟺ `a² ≤ 4q` (`q > 0`). -/
theorem positividade_iff_hasse {a q : ℤ} (hq : 0 < q) :
    (∀ m n : ℤ, 0 ≤ m ^ 2 - a * m * n + q * n ^ 2) ↔ a ^ 2 ≤ 4 * q := by
  constructor
  · intro h
    have := h a 2
    nlinarith
  · intro h m n
    nlinarith [sq_nonneg (2 * q * n - a * m), mul_nonneg (sub_nonneg.mpr h) (sq_nonneg m)]

/-- **Todas as curvas sobre `𝔽₁₃` têm a forma do grau positiva.** -/
theorem positividade_F13 (a b : ℕ) (ha : a < 13) (hb : b < 13) (hd : (4 * a ^ 3 + 27 * b ^ 2) % 13 ≠ 0) :
    ∀ m n : ℤ, 0 ≤ m ^ 2 - Geometrias.traco 13 a b * m * n + 13 * n ^ 2 :=
  (positividade_iff_hasse (by norm_num)).mpr (Geometrias.hasse_F13 a ha b hb hd)

/-! ## 5. A ponte com BSD: a RH local dos fatores de `L(E, s)` -/

/-- Os primos de `5` a `97`. -/
def primos97 : List ℕ := [5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

/-- **`E₀: y² = x³ − x`**: `a_p² ≤ 4p` em todo primo `5 ≤ p ≤ 97`. -/
theorem hasse_E0_97 : ∀ p ∈ primos97, Geometrias.traco p (p - 1) 0 ^ 2 ≤ 4 * p := by
  decide +kernel

/-- **`E₁: y² = x³ − 2`**: `a_p² ≤ 4p` em todo primo `5 ≤ p ≤ 97`. -/
theorem hasse_E1_97 : ∀ p ∈ primos97, Geometrias.traco p 0 (p - 2) ^ 2 ≤ 4 * p := by
  decide +kernel

/-- **Multiplicação complexa**: `a_p(E₀) = 0` para `p ≡ 3 (mod 4)`, `5 ≤ p ≤ 97`. -/
theorem E0_supersingular_97 : ∀ p ∈ primos97, p % 4 = 3 → Geometrias.traco p (p - 1) 0 = 0 := by
  decide +kernel

end ClayRiemannProof.Maquina
