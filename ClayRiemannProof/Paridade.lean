import ClayRiemannProof.PrimeiroFora

/-!
# Zeros fora da reta vêm aos pares na mesma altura: a contagem só falha de 2 em 2

Se `ρ` é zero não trivial com `Re ρ ≠ ½`, a torção `s ↦ 1 − s̄` dá outro zero, `1 − ρ̄`, com a **mesma** parte
imaginária e parte real `1 − Re ρ ≠ Re ρ` (`Zeta.Symmetry.torcao_mem_Z`). Numa janela de alturas `T₁ < Im s ≤ T₂`
a torção é uma involução sem pontos fixos dos zeros fora da reta, logo eles são em número par:

* `fora_par`: o número de zeros fora da reta numa janela (`1 ≤ T₁`) é par;
* `contagem_soma`: zeros na janela = zeros na reta + zeros fora da reta (conjuntos finitos, `PrimeiroFora.zeros_finitos`);
* `furo_de_dois`: se a contagem total `N(T₂) − N(T₁)` não bate com os zeros achados na reta, a diferença é **pelo menos
  2** — um zero fora da reta aparece na contagem de Turing como um déficit de 2 (o par `ρ`, `1 − ρ̄`), nunca de 1;
* `contagem_fecha`: se bate, não há zero fora da reta na janela.

É a forma exata do que as contagens locais dos nós (seção 25 do README) testam. Os números dessas contagens vêm da
Arb, fora do kernel. Nada aqui prova ou refuta RH. `OPEN_MATH = true`.
-/

namespace ClayRiemannProof.Paridade

open Complex Set ClayRiemannProof.Zeta.Symmetry

/-- **Involução sem pontos fixos ⟹ cardinalidade par** (forma com `n` explícito, por indução forte). -/
theorem card_par_aux {α : Type*} [DecidableEq α] (f : α → α) :
    ∀ n : ℕ, ∀ S : Finset α, S.card = n → (∀ x ∈ S, f x ∈ S) → (∀ x ∈ S, f (f x) = x) →
      (∀ x ∈ S, f x ≠ x) → Even n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn hS hinv hfix
    rcases S.eq_empty_or_nonempty with h | ⟨x, hx⟩
    · rw [← hn, h, Finset.card_empty]
      exact ⟨0, rfl⟩
    · have hfx : f x ∈ S.erase x := Finset.mem_erase.mpr ⟨hfix x hx, hS x hx⟩
      have hc1 : ((S.erase x).erase (f x)).card = (S.erase x).card - 1 := Finset.card_erase_of_mem hfx
      have hc2 : (S.erase x).card = S.card - 1 := Finset.card_erase_of_mem hx
      have hpos : 1 ≤ (S.erase x).card := Finset.card_pos.mpr ⟨f x, hfx⟩
      have hmem : ∀ y ∈ (S.erase x).erase (f x), y ∈ S ∧ y ≠ x ∧ y ≠ f x := by
        intro y hy
        rw [Finset.mem_erase, Finset.mem_erase] at hy
        exact ⟨hy.2.2, hy.2.1, hy.1⟩
      have hT : ∀ y ∈ (S.erase x).erase (f x), f y ∈ (S.erase x).erase (f x) := by
        intro y hy
        obtain ⟨hyS, hyx, hyfx⟩ := hmem y hy
        rw [Finset.mem_erase, Finset.mem_erase]
        refine ⟨fun h => hyx ?_, fun h => hyfx ?_, hS y hyS⟩
        · rw [← hinv y hyS, h, hinv x hx]
        · rw [← hinv y hyS, h]
      obtain ⟨k, hk⟩ := ih ((S.erase x).erase (f x)).card (by omega) _ rfl hT
        (fun y hy => hinv y (hmem y hy).1) (fun y hy => hfix y (hmem y hy).1)
      exact ⟨k + 1, by omega⟩

/-- Zeros não triviais na janela de alturas `T₁ < Im s ≤ T₂`. -/
def NaJanela (T₁ T₂ : ℝ) : Set ℂ := {s | s ∈ Z ∧ T₁ < s.im ∧ s.im ≤ T₂}

/-- Os da reta crítica. -/
def NaReta (T₁ T₂ : ℝ) : Set ℂ := {s | s ∈ NaJanela T₁ T₂ ∧ s.re = 1 / 2}

/-- Os fora da reta crítica. -/
def Fora (T₁ T₂ : ℝ) : Set ℂ := {s | s ∈ NaJanela T₁ T₂ ∧ s.re ≠ 1 / 2}

/-- A janela é finita (`1 ≤ T₁`): está dentro do retângulo `[0, 1] × [1, T₂]`. -/
theorem naJanela_finita {T₁ T₂ : ℝ} (h : 1 ≤ T₁) : (NaJanela T₁ T₂).Finite := by
  refine (ClayRiemannProof.PrimeiroFora.zeros_finitos T₂).subset ?_
  rintro s ⟨⟨hz, h0, h1⟩, ha, hb⟩
  exact ⟨⟨⟨h0.le, h1.le⟩, ⟨by linarith, hb⟩⟩, hz⟩

theorem fora_finito {T₁ T₂ : ℝ} (h : 1 ≤ T₁) : (Fora T₁ T₂).Finite :=
  (naJanela_finita h).subset fun _ hs => hs.1

theorem naReta_finita {T₁ T₂ : ℝ} (h : 1 ≤ T₁) : (NaReta T₁ T₂).Finite :=
  (naJanela_finita h).subset fun _ hs => hs.1

/-- A torção não muda a altura. -/
theorem im_torcao (s : ℂ) : (torcao s).im = s.im := by simp [torcao]

/-- A torção leva zeros fora da reta da janela em zeros fora da reta da mesma janela. -/
theorem torcao_fora {T₁ T₂ : ℝ} {s : ℂ} (hs : s ∈ Fora T₁ T₂) : torcao s ∈ Fora T₁ T₂ := by
  obtain ⟨⟨hz, ha, hb⟩, hr⟩ := hs
  refine ⟨⟨torcao_mem_Z hz, by rw [im_torcao]; exact ha, by rw [im_torcao]; exact hb⟩, ?_⟩
  rw [re_torcao]
  intro h
  apply hr
  linarith

/-- Fora da reta, a torção não tem ponto fixo. -/
theorem torcao_ne {T₁ T₂ : ℝ} {s : ℂ} (hs : s ∈ Fora T₁ T₂) : torcao s ≠ s := fun h =>
  hs.2 ((torcao_fixo_iff s).mp h)

/-- **Os zeros fora da reta numa janela são em número par.** -/
theorem fora_par {T₁ T₂ : ℝ} (h : 1 ≤ T₁) : Even (Fora T₁ T₂).ncard := by
  classical
  have hfin := fora_finito (T₂ := T₂) h
  rw [Set.ncard_eq_toFinset_card _ hfin]
  refine card_par_aux torcao _ _ rfl ?_ ?_ ?_
  · intro x hx
    rw [Set.Finite.mem_toFinset] at hx ⊢
    exact torcao_fora hx
  · intro x _
    exact torcao_torcao x
  · intro x hx
    rw [Set.Finite.mem_toFinset] at hx
    exact torcao_ne hx

/-- Janela = reta ∪ fora da reta. -/
theorem janela_uniao (T₁ T₂ : ℝ) : NaJanela T₁ T₂ = NaReta T₁ T₂ ∪ Fora T₁ T₂ := by
  ext s
  constructor
  · intro hs
    by_cases hr : s.re = 1 / 2
    · exact Or.inl ⟨hs, hr⟩
    · exact Or.inr ⟨hs, hr⟩
  · rintro (hs | hs)
    · exact hs.1
    · exact hs.1

/-- **Contagem total = na reta + fora da reta.** -/
theorem contagem_soma {T₁ T₂ : ℝ} (h : 1 ≤ T₁) :
    (NaJanela T₁ T₂).ncard = (NaReta T₁ T₂).ncard + (Fora T₁ T₂).ncard := by
  rw [janela_uniao]
  exact Set.ncard_union_eq (Set.disjoint_left.mpr fun _ h1 h2 => h2.2 h1.2) (naReta_finita h) (fora_finito h)

/-- **Um furo na contagem é de pelo menos 2**: se a contagem total não bate com os zeros na reta, faltam ao menos
dois (um zero fora da reta `ρ` e o seu par `1 − ρ̄`, na mesma altura). -/
theorem furo_de_dois {T₁ T₂ : ℝ} (h : 1 ≤ T₁) (hne : (NaJanela T₁ T₂).ncard ≠ (NaReta T₁ T₂).ncard) :
    (NaReta T₁ T₂).ncard + 2 ≤ (NaJanela T₁ T₂).ncard := by
  have hs := contagem_soma (T₂ := T₂) h
  obtain ⟨k, hk⟩ := fora_par (T₂ := T₂) h
  omega

/-- **Contagem que fecha: nenhum zero fora da reta na janela.** -/
theorem contagem_fecha {T₁ T₂ : ℝ} (h : 1 ≤ T₁) (heq : (NaJanela T₁ T₂).ncard = (NaReta T₁ T₂).ncard) :
    Fora T₁ T₂ = ∅ := by
  have hs := contagem_soma (T₂ := T₂) h
  exact (Set.ncard_eq_zero (fora_finito h)).mp (by omega)

/-- **Fechamento a partir das duas contagens**: `k` zeros na janela (contagem de Turing) e pelo menos `k` deles
achados na reta (trocas de sinal de `Z`) ⟹ nenhum zero fora da reta na janela. -/
theorem fecha_de_contagens {T₁ T₂ : ℝ} {k : ℕ} (h : 1 ≤ T₁) (hN : (NaJanela T₁ T₂).ncard = k)
    (hL : k ≤ (NaReta T₁ T₂).ncard) : Fora T₁ T₂ = ∅ := by
  have hs := contagem_soma (T₂ := T₂) h
  exact (Set.ncard_eq_zero (fora_finito h)).mp (by omega)

/-- **O nó mais forte da faixa (o aglomerado), seção 25**: a Arb deu `N(T_a) = 12363153449050` e
`N(T_b) = 12363153449061` (11 zeros na janela) e achou os 11 na reta (hipóteses). -/
theorem no_aglomerado_sem_fora
    (hN : (NaJanela 3000175335583.396935101093095 3000175335586.100401896311926).ncard = 11)
    (hL : 11 ≤ (NaReta 3000175335583.396935101093095 3000175335586.100401896311926).ncard) :
    Fora 3000175335583.396935101093095 3000175335586.100401896311926 = ∅ :=
  fecha_de_contagens (by norm_num) hN hL

end ClayRiemannProof.Paridade
