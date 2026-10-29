# Hipótese de Riemann — prova (Lean 4 / Mathlib)

Depende do enunciado em [`ShantiDraconis/clay-riemann-statement`](https://github.com/ShantiDraconis/clay-riemann-statement),
fixado no commit `47fe26a`. O alvo é `ClayRiemann.Statement`, sem redefinição
(`abbrev Target := ClayRiemann.Statement`, que é o `RiemannHypothesis` da Mathlib).

Estado: sem prova. `OPEN_MATH = true`. Nada abaixo prova RH: há uma equivalência exata
(`Target ↔ Gap`) e um resultado condicional a um teorema externo.

Regras: nenhum `sorry`, `axiom`, `native_decide` ou marcador; `#print axioms ClayRiemannProof.main` fixado
com `#guard_msgs` quando `main` existir.

Prêmio: a formalização é material suplementar. O Clay e a AMS só consideram soluções publicadas
em periódico referado; o Clay espera ainda dois anos e aceitação geral.

## Auditoria

`ClayRiemannProof/Audit.lean` (importado por último pela raiz) fixa, com `#guard_msgs`, a saída real
de `#print axioms` de cada uma das 311 declarações públicas acrescentadas. Todas dependem apenas de
`[propext, Classical.choice, Quot.sound]` (os axiomas padrão que o próprio Mathlib usa; `Real` já
depende deles). Verificado com Lean 4.36.0-rc2 e Mathlib `8fe7ce4`.

## 1. Critério de Báez-Duarte: `Target ↔ Gap` (equivalência, teorema)

Arquivo: `ClayRiemannProof/BaezDuarteGap.lean`.

```lean
def Gap : Prop := (⨅ N, DN N) = 0
theorem gap_iff_tendsto : Gap ↔ Tendsto DN atTop (𝓝 0)
theorem target_of_gap   : Gap → Target
theorem gap_of_target   : Target → Gap
theorem target_iff_gap  : Target ↔ Gap
```

`DN N = inf_{c ∈ ℝ^N} ∫_{(0,∞)} (χ(t) − Σ_{k=1}^{N} c_k {1/(k t)})² dt`, com `χ = 𝟙_(0,1]`
(`ClayRiemannProof/BaezDuarte/Defs.lean`); o integrando é sempre integrável
(`Faithful.integrable_residual`), logo é a integral de Lebesgue genuína.

**O que é**: o critério de Nyman–Beurling na forma de Báez-Duarte (2003), provado nos dois sentidos
contra a `riemannZeta` e o `RiemannHypothesis` da Mathlib.

* Suficiência `Gap → Target` (`BaezDuarte/Sufficiency.lean`): transformadas de Mellin de `χ` e
  `ρ_k` (`Zeta/Strip.lean`, `BaezDuarte/MellinRho.lean`), uma desigualdade de Cauchy–Schwarz
  elementar e a equação funcional da Mathlib.
* Necessidade `Target → Gap` (`BaezDuarte/Necessity.lean`): fórmula espectral de `D_N`
  (Plancherel de Mellin, `Fourier/*`, `BaezDuarte/Spectral.lean`), mollificador de Möbius suavizado,
  fórmula de Perron suavizada com deslocamento de contorno (`Zeta/PerronSmoothed.lean`), cotas sob RH
  do tipo Titchmarsh 14.2 / Lindelöf (`Zeta/LogBoundRH.lean`), `Γ` em faixas verticais e
  Phragmén–Lindelöf para `ζ(s)/ζ(s+ε)` (`Zeta/GammaVertical.lean`, `Zeta/Ratio.lean`),
  convergência dominada.

**O que NÃO é**: não é prova de RH. `Gap` (`inf_N D_N = 0`) continua aberto; o teorema só diz que
ele tem exatamente a força de RH.

**Origem** (ATK kernel, espelho público do M-Core, `imports/M-Core/atk-kernel/ATK/`):

| aqui | ATK kernel |
|---|---|
| `BaezDuarte/Defs.lean` | `Conditional/Riemann.lean` (definições) + `RiemannConcrete.lean` (monotonia, limite) |
| `BaezDuarte/Faithful.lean` | `RiemannFaithful.lean` |
| `Zeta/Strip.lean` | `ZetaStrip.lean` |
| `BaezDuarte/MellinRho.lean` | `MellinRho.lean` |
| `BaezDuarte/Sufficiency.lean` | `BaezDuarteBridge.lean` (M-Core `9e27bb5`) |
| `Fourier/PlancherelL1L2.lean` | `PlancherelL1L2.lean` |
| `Fourier/MellinPlancherel.lean` | `MellinPlancherel.lean` |
| `BaezDuarte/Spectral.lean` | `EspectralDN.lean` |
| `BaezDuarte/NecessityFramework.lean` | `NecessidadeBD.lean` |
| `Zeta/Bounds.lean` | trechos de `ZetaRetangulo.lean` (`Hr`, `norm_H_le`, `Hr_le`) e `ZetaRegiao.lean` (`zeta_eq`, `norm_zeta_le`) |
| `Zeta/LogBoundRH.lean` | `RHLogZeta.lean` |
| `Zeta/GammaVertical.lean` | `GammaVertical.lean` |
| `Zeta/Ratio.lean` | `RazaoZeta.lean` |
| `Zeta/PerronSmoothed.lean` | `PerronSuave.lean` |
| `BaezDuarte/Necessity.lean` | `NecessidadeRH.lean` (M-Core `f81c6ef`) |

Mudanças na portagem: espaços de nomes `ATK.*` → `ClayRiemannProof.*`; `O1_iff_iInf_zero` →
`tendsto_zero_iff_iInf_eq_zero`; `baezDuarteCriterion` → `baezDuarte_sufficiency`; três ajustes de
compatibilidade com o Mathlib atual (anotação de tipo em `Bounds.integrableOn_g`, `differentiableAt_F`
e `continuous_KK_line` reescritos sem `fun_prop`/`Continuous.div` por timeout de elaboração).
Retirado por não ser necessário ao critério: a "teoria de estados" do ATK (`Indeterminacy*`,
`RiemannStates`, `O1_iff_dissipacao`, `riemann_of_not_finito`), as pontes condicionais
`BaezDuarteCriterion` / `UniformLogBound`, `bdDistSq_iff_rh` (`BDDistSqPort`) e o resto de
`ZetaSimetria` / `ZetaRetangulo` / `ZetaRegiao`.

**Axiomas**: `[propext, Classical.choice, Quot.sound]` (todas as declarações; ver `Audit.lean`).

## 2. RH condicional ao quasi-RH `1/8–7/8` (condicional a resultado externo)

Arquivo: `ClayRiemannProof/QuasiRH.lean`.

```lean
def OpenAIQuasiRH78 : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬ ∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
    1 / 8 ≤ s.re ∧ s.re ≤ 7 / 8
def NoZero_half_78 : Prop :=      -- nenhum zero não trivial com 1/2 < Re s ≤ 7/8
def NoZero_right_half : Prop :=   -- nenhum zero não trivial com Re s > 1/2

theorem target_iff_noZero_right_half : Target ↔ NoZero_right_half          -- incondicional
theorem target_iff_noZero_half_78 (hQ : OpenAIQuasiRH78) : Target ↔ NoZero_half_78
theorem openAIQuasiRH78_of_target : Target → OpenAIQuasiRH78               -- sanidade
theorem riemannZeta_one_sub_eq_zero : ζ(s) = 0 → 0 < Re s → Re s < 1 → ζ(1 − s) = 0
```

**O que é**: `OpenAIQuasiRH78` é um **resultado externo** — OpenAI, versão verificada em Lean datada
de 2026-09-30, anunciada em 2026-10-06; reportagem: Quanta Magazine, 2026-10-19,
<https://quantamagazine.org/ai-proved-the-quasi-riemann-hypothesis-what-happens-now-20261019>.
Aqui ele entra só como hipótese nomeada (`def … : Prop`, nunca `axiom`). Sob essa hipótese, RH
equivale a excluir zeros não triviais com `1/2 < Re s ≤ 7/8` (o lado esquerdo da faixa vem de graça
pela simetria `s ↦ 1 − s` da equação funcional da Mathlib, `target_iff_noZero_right_half`).
`openAIQuasiRH78_of_target` mostra que a hipótese é consequência de RH, portanto não é
trivialmente falsa (refutá-la refutaria RH).

**O que NÃO é**: não é prova de RH, nem verificação do resultado da OpenAI (cuja formalização não
foi conferida por este repositório). Segundo a reportagem, a versão posterior (2026-10-05) afirma
só `1/12 ≤ Re s ≤ 11/12` e não foi verificada em Lean.

**Origem**: escrito neste repositório (a parte da equação funcional segue o argumento de
`riemannHypothesis_of_strip` de `ATK/BaezDuarteBridge.lean`).

**Axiomas**: `[propext, Classical.choice, Quot.sound]`.

## 3. Identidade de Nyman–Beurling para `θ` real (teorema)

Arquivo: `ClayRiemannProof/BaezDuarte/NymanBeurling.lean`.

```lean
def rhoθ (θ t : ℝ) : ℂ := {θ / t}
def fθ   (θ t : ℝ) : ℂ := {θ / t} − θ {1 / t}

theorem mellin_rhoθ   (hθ : 0 < θ) (0 < Re s < 1) : mellin (rhoθ θ) s = −(θ^s ζ(s) / s)
theorem fθ_eq_zero_of_one_lt (0 < θ ≤ 1) (1 < t) : fθ θ t = 0
theorem mellin_fθ     (hθ : 0 < θ) (0 < Re s < 1) : mellin (fθ θ) s = (θ − θ^s) ζ(s) / s
theorem integral_Ioc_fθ (0 < θ ≤ 1) (0 < Re s < 1) :
    ∫ t in Ioc 0 1, t^(s−1) • fθ θ t = (θ − θ^s) ζ(s) / s
theorem integral_Ioc_fθ_eq_zero : ζ(s) = 0 → ∫ t in Ioc 0 1, t^(s−1) • fθ θ t = 0
```

**O que é**: a transformada de Mellin das funções `f_θ` do critério de Nyman (1950) e Beurling (1955),
para todo `θ ∈ (0,1]` real — a família contínua da qual Báez-Duarte (2003) extrai a enumerável
`θ = 1/k` usada em `MellinRho.mellin_rho` (que é o caso `θ = 1/k` de `mellin_rhoθ`). `f_θ` se anula em
`(1,∞)`, então a transformada em `(0,∞)` é a integral em `(0,1]`, e um zero de `ζ` na faixa anula a
integral contra `t^{s−1}` de toda a família. A prova reaproveita `MellinRho.mellin_fr_neg`,
`Strip.H_eq_zeta` e as mudanças de variável de Mellin da Mathlib (`mellin_comp_mul_left`,
`mellin_comp_inv`).

**O que NÃO é**: não é prova de RH nem um passo novo em direção a ela; é a identidade clássica que liga
a família `f_θ` aos zeros de `ζ`. A identidade vale na faixa `0 < Re s < 1`; a forma
`∫_0^1 {θ/x} x^{s−1} dx` sozinha (sem o termo `θ{1/x}`) tem também o termo `θ/(s−1)`.

**Origem**: escrito neste repositório.

**Axiomas**: `[propext, Classical.choice, Quot.sound]` (14 declarações; ver `Audit.lean`).

