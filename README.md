# Hipótese de Riemann — prova (Lean 4 / Mathlib)

Depende do enunciado em [`ShantiDraconis/clay-riemann-statement`](https://github.com/ShantiDraconis/clay-riemann-statement),
fixado no commit `47fe26a`. O alvo é `ClayRiemann.Statement`, sem redefinição
(`abbrev Target := ClayRiemann.Statement`, que é o `RiemannHypothesis` da Mathlib).

Estado: sem prova. `OPEN_MATH = true`. Nada abaixo prova RH: há equivalências exatas (as treze estão reunidas
em `Bridges.pontes`, seção 8), um resultado condicional a um teorema externo e o mundo `Z = 13` certificado.

Regras: nenhum `sorry`, `axiom`, `native_decide` ou marcador; `#print axioms ClayRiemannProof.main` fixado
com `#guard_msgs` quando `main` existir.

Prêmio: a formalização é material suplementar. O Clay e a AMS só consideram soluções publicadas
em periódico referado; o Clay espera ainda dois anos e aceitação geral.

## Auditoria

`ClayRiemannProof/Audit.lean` (importado por último pela raiz) fixa, com `#guard_msgs`, a saída real
de `#print axioms` de cada uma das 588 declarações públicas acrescentadas; `ClayRiemannProof/AuditThirteen.lean`
faz o mesmo para as 253 da cadeia certificada até a altura 13 (841 guardas no total). Todas dependem apenas de
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

**O que NÃO é**: não é prova de RH, nem verificação do resultado da OpenAI. O enunciado formalizado
por eles é `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` (`ζ(s) ≠ 0` para `Re s > 7/8`), em
[`openai/math`](https://github.com/openai/math), pasta `lean/`, commit `1581d4c`, com Lean `v4.34.1` e
outra Mathlib; ele não é importado nem recompilado aqui. O artigo de 2026-10-05 da mesma série expõe
separadamente a etapa intermediária `Re s > 11/12`.

**Origem**: escrito neste repositório (a parte da equação funcional segue o argumento de
`riemannHypothesis_of_strip` de `ATK/BaezDuarteBridge.lean`).

**Axiomas**: `[propext, Classical.choice, Quot.sound]`.

## 3. A ponte com as aritméticas finitas (teorema)

Arquivos: `ClayRiemannProof/FiniteWorlds.lean` e `ClayRiemannProof/Zeta/Symmetry.lean`.

```lean
abbrev Sat (Z : ℕ) := Fin (Z + 1)                 -- {0,…,Z}: Z é o último inteiro deste mundo
def satAdd (a b : Sat Z) : Sat Z                  -- a ⊕ b = min Z (a + b)
theorem ultimo_absorve (a : Sat Z) : satAdd (Fin.last Z) a = Fin.last Z
theorem cancelamento_falha (hZ : 1 ≤ Z) : ∃ a b c, satAdd a c = satAdd b c ∧ a ≠ b
theorem nao_ha_ultimo_inteiro : ¬ ∃ Z : ℕ, ∀ n : ℕ, n ≤ Z

def RHateZ (Z : ℕ) : Prop                         -- todo zero não trivial com |Im s| ≤ Z está em Re s = 1/2
def RHnoMundo (Z : ℕ) : Prop := ∀ h : Sat Z, RHateZ h.val
theorem rhNoMundo_iff : RHnoMundo Z ↔ RHateZ Z
theorem target_iff_todos_os_mundos : Target ↔ ∀ Z : ℕ, RHnoMundo Z
theorem not_target_iff_um_mundo : ¬ Target ↔ ∃ Z : ℕ, ¬ RHnoMundo Z
theorem rhNoMundo_zero : RHnoMundo 0              -- certificado: não há zero não trivial real
def PlattTrudgian2021 : Prop := RHateZ 3000175332800
theorem rhNoMundo_platt_trudgian (h : PlattTrudgian2021) : RHnoMundo 3000175332800
```

**O que é**: uma aritmética finita com último inteiro `Z` existe sem contradição (soma saturada, em que
`Z ⊕ 1 = Z`), ao preço do cancelamento. Cada mundo `Sat Z` enxerga os zeros de altura `|Im s| ≤ Z`. O
enunciado do Clay é exatamente "RH vale em todo mundo finito", e RH é falsa exatamente quando falha em
**um** mundo finito: um contraexemplo, se existir, mora numa altura finita. O mundo `Z = 0` está certificado
(a reta real não tem zero não trivial). O mundo `Z = 3 000 175 332 800` vale condicionalmente à
verificação de Platt e Trudgian (*The Riemann hypothesis is true up to 3·10¹²*, Bull. London Math. Soc. 53
(2021) 792–797), que entra como hipótese nomeada.

**O que NÃO é**: nenhum mundo finito isolado implica o enunciado do Clay; a passagem de "cada `Z`" para
"todo `Z`" é o problema em aberto. Um último inteiro dentro de `ℕ` é contraditório
(`nao_ha_ultimo_inteiro`) e não é usado.

**Origem**: `Zeta/Symmetry.lean` é o `ATK/ZetaSimetria.lean` do kernel ATK (espelho público, M-Core
`390e378`), portado; `FiniteWorlds.lean` é novo. A aritmética saturada segue `ATK/ZeroClasses/Finito.lean`
(`satAdd_assoc`, `terminal_absorve`, `cancelamento_falha`).

**Axiomas**: `Sat` e `le_ultimo` não dependem de nenhum; `satAdd`, `satAdd_comm`, `satAdd_assoc` e
`nao_ha_ultimo_inteiro` usam `[propext, Quot.sound]`; os demais `[propext, Classical.choice, Quot.sound]`.
Todas as 68 declarações novas estão fixadas em `ClayRiemannProof/Audit.lean`.

## 4. Nenhum zero de `ζ` na faixa crítica até a altura 13; o mundo `Z = 13` (teorema)

Arquivo: `ClayRiemannProof/HeightThirteen.lean` (certificados em `ClayRiemannProof/CertifiedZeros/`, aritmética
intervalar em `ClayRiemannProof/Cert/`, Euler–Maclaurin em `ClayRiemannProof/EulerMaclaurin/`, faixa baixa em
`ClayRiemannProof/LowStrip/Disc.lean`).

```lean
theorem faixa_ate_13 : ∀ z ∈ ret (1/2) 1 (43/50) 13, 1/50 ≤ ‖riemannZeta z‖   -- [½, 1] × [43/50, 13]
theorem faixa_sem_zeros {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (ht : |s.im| ≤ 13) :
    riemannZeta s ≠ 0
theorem zeros_acima_13 : ∀ s : ℂ, riemannZeta s = 0 → (¬ ∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 →
    13 < |s.im|
theorem rhNoMundo_13 : FiniteWorlds.RHnoMundo 13                              -- certificado (vacuamente)

-- peças usadas
theorem LowStrip.Disc.zeta_ne_zero_disco : 0 < Re s → ‖s − 1‖ < 2 Re s → ζ(s) ≠ 0
theorem LowStrip.Disc.zeta_ne_zero_baixo : 0 < Re s → Re s < 1 → (Im s)² < 3/4 → ζ(s) ≠ 0
theorem EulerMaclaurin.General.norm_zeta_sub_EM_le   -- resto explícito de Euler–Maclaurin de ordem M
theorem CertifiedZeros.Evaluation.mem_zetaIG         -- ζ(σ + it) num retângulo racional (σ, t ∈ ℚ)
theorem CertifiedZeros.Rectangle.peca_ret            -- malha + Cauchy ⟹ |ζ| ≥ δ num retângulo
```

**O que é**: uma verificação numérica rigorosa, feita inteiramente pelo kernel do Lean, de que `ζ` (a
`riemannZeta` da Mathlib) não se anula em `0 < Re s < 1`, `|Im s| ≤ 13`. Três partes:

* faixa baixa `(Im s)² < 3/4`: a região sem zeros `|s − 1| < 2·Re s` (de `ζ(s) = s/(s−1) − s·H(s)` com
  `|H(s)| ≤ 1/(2 Re s)`, já em `Zeta/Bounds.lean`) e a tensão `s ↦ 1 − s`;
* `[½, 1] × [43/50, 13]`: 50 retângulos com malhas de centros, 930 avaliações certificadas de `ζ(σ + it)`
  (`σ`, `t` racionais) por Euler–Maclaurin de ordem `M ≤ 10` com resto explícito; `n^{−σ}` por certificado de
  raiz racional, `log n` pela série de `atanh`, `e^{iθ}` por Taylor com redução por `2π`; tudo em aritmética
  intervalar sobre `ℚ`, decidida por `decide +kernel` (sem `native_decide`). Entre os centros: Cauchy
  (`‖ζ′‖ ≤ B/r`, com `B` uma cota grosseira certificada) e o valor médio dão `|ζ| ≥ 1/50`;
* `0 < Re s < ½` pela torção `s ↦ 1 − s̄`, `Im s < 0` pela conjugação, e `Re s ≤ 0`, `Re s ≥ 1` pelos
  extremos fechados de `Zeta/Symmetry.lean`.

Daí `zeros_acima_13` (todo zero não trivial, no sentido do enunciado da Mathlib, tem `|Im s| > 13`) e
`rhNoMundo_13`: o mundo finito `Z = 13` da seção 3 fica certificado, sem hipótese (até aqui só `Z = 0` estava).
O primeiro zero não trivial conhecido tem altura ≈ 14,1347, logo a altura 13 está abaixo dele.

**O que NÃO é**: não é prova de RH. O mundo `Z = 13` está certificado **vacuamente**: não há zero não trivial com
`|Im s| ≤ 13`, então nenhum zero é testado contra a reta crítica. Nenhum zero na reta é localizado aqui (o zero
perto de `½ + 14,1347i` do kernel ATK não foi portado), e o mundo `Z = 3 000 175 332 800` continua condicional a
`PlattTrudgian2021`. RH é `∀ Z, RHnoMundo Z`; um mundo finito isolado não a implica. `OPEN_MATH = true`.

**Origem** (ATK kernel, espelho público do M-Core `390e378`, `imports/M-Core/atk-kernel/ATK/`):

| aqui | ATK kernel |
|---|---|
| `Cert/Interval.lean` | `Cert/Intervalo.lean` (sem `IR.inv`, `absMax`, `IC.sub`, `normMax` e teoremas) |
| `Cert/Transcendental.lean` | `Cert/Transc.lean` (sem `logI`, `sqrtOk`) |
| `EulerMaclaurin/FirstOrder.lean` | `BLEulerMaclaurin.lean` |
| `EulerMaclaurin/General.lean` | `EMGeral.lean` |
| `CertifiedZeros/EulerMaclaurinData.lean` | trechos de `ZeroCertificado.lean` (`Lg`, `fase`, `Btab`, `pochQ`, `PcR`, `Qcoef`, `CbR`, specs, `EM_decomp`) |
| `CertifiedZeros/CrudeBound.lean` | trecho (§5) de `ZeroClasses/QuartoGeral.lean` (`cota_geral`, `cotaQ`) |
| `CertifiedZeros/Evaluation.lean` | `ZeroClasses/FaixaAval.lean` + `rootOk`, `mem_root`, `cpow_gen` de `DeltaCertificado.lean` + `dz`, `nMinSq`, `le_norm_de` de `ZeroClasses/QuartoAval.lean` |
| `CertifiedZeros/Rectangle.lean` | `ZeroClasses/FaixaGeral.lean` + `certificado_malha`, `certificado_derivada` de `ZeroClasses/Regions.lean` + `difOn_zeta` de `ZeroCritico.lean` + `cobre` de `ZeroClasses/QuartoGeral.lean` |
| `CertifiedZeros/Pieces1.lean`, `Pieces2.lean`, `Pieces3.lean` | `ZeroClasses/FaixaPecas1.lean`, `FaixaPecas2.lean`, `FaixaPecas3.lean` (parâmetros numéricos intactos) |
| `LowStrip/Disc.lean` | `zeta_ne_zero_disco`, `zeta_ne_zero_baixo` de `ZetaRetangulo.lean` |
| `HeightThirteen.lean` | `ZeroClasses/Faixa.lean` (`faixa_ate_13`, `cota_metade`, `im_torcao`, `sem_zeros_pos`, `faixa_sem_zeros`) |

Mudanças na portagem: espaços de nomes `ATK.*` → `ClayRiemannProof.<Pasta>.<Arquivo>`; `import Mathlib` → módulos
específicos (inclusive `Mathlib.Analysis.Complex.Liouville`, para a cota de Cauchy);
`Polynomial.eval₂_finset_sum` → `Polynomial.eval₂_finsetSum` (renomeado no Mathlib atual); um `simp [ha0]` com
argumento não usado → `simp`. Reusados sem duplicar: `Zeta/Strip.lean` (`H`, `H_eq_zeta`), `Zeta/Bounds.lean`
(`Hr`, `norm_H_le`, `Hr_le`), `Zeta/Symmetry.lean` (`torcao`, `Z`, `torcao_mem_Z`, `zero_trivial_de_re_nao_pos`).
`zeros_acima_13` foi reenunciado na forma do enunciado da Mathlib (no ATK: `∀ ρ ∈ Z, 13 < |ρ.im|`);
`rhNoMundo_13` é novo. Não portados, por estarem fora do fecho mínimo: `verificado_13` (usa
`ZeroClasses/Escalas.lean`), `primeiro_zero_entre` (usa o zero certificado de `ZeroCritico.lean`), `m_pos_ate_13` e
`novo_primeiro_ponto_14` (usam os mínimos `m_n` de `ZeroClasses/Regions.lean`); nem `ZeroClasses/FinalAudit.lean`,
`Hipotetico.lean`, `RHTerminal.lean` ou os arquivos de "estados" do ATK, que alguns desses arquivos importavam sem usar.

**Axiomas**: `faixa_sem_zeros`, `zeros_acima_13` e `rhNoMundo_13` dependem de `[propext, Classical.choice, Quot.sound]`.
Das 252 declarações novas, 244 usam esses três; `IR`, `IC`, `IR.pt`, `IR.neg` e `IC.pt` não dependem de nenhum;
`irootAux` e `iroot` usam `[propext]`; `dz` usa `[propext, Quot.sound]`. `decide +kernel` não acrescenta axioma
(não há `Lean.ofReduceBool`). Todas estão fixadas em `ClayRiemannProof/AuditThirteen.lean`.

## 5. O truncamento depois do infinito: `D_ω` (equivalência, teorema)

Arquivo: `ClayRiemannProof/HyperTruncation.lean` (hiper-reais `ℝ*` da Mathlib).

```lean
noncomputable def DOmega : ℝ* := ofSeq (fun n => DN n)       -- D truncado no hipernatural ω = [n ↦ n]
def IsInfinitesimal (x : ℝ*) : Prop := ∀ r : ℝ, 0 < r → |x| < r
theorem target_iff_DOmega_infinitesimal : Target ↔ IsInfinitesimal DOmega
theorem nat_lt_omega (n : ℕ) : (n : ℝ*) < ω                    -- ω vem depois de todo inteiro comum
theorem nat_lt_omega_sub_one (n : ℕ) : (n : ℝ*) < ω - 1        -- não há primeiro inteiro infinito
```

**O que é**: o critério de Báez-Duarte trunca em `N` termos; aqui o truncamento é feito num inteiro **depois de
todos os inteiros comuns**, o hipernatural `ω`. O enunciado do Clay equivale a `D_ω` ser infinitesimal. Não existe
primeiro inteiro infinito (`ω − 1` também é infinito), então `ω` é um representante do "depois do infinito", não
um ponto único.

**O que NÃO é**: reformulação de `target_iff_gap`, não prova de RH; decidir se `D_ω` é infinitesimal é o mesmo
problema. **Origem**: novo neste repositório. **Axiomas**: `[propext, Classical.choice, Quot.sound]`.

## 6. O segundo universo `j`: números bicomplexos (equivalência, teorema)

Arquivo: `ClayRiemannProof/Bicomplex.lean`.

```lean
structure BC where c1 c2 : ℂ                     -- z₁ + j z₂, j² = −1, j comuta com i
theorem k_sq : k * k = 1                          -- k = i j
theorem divisor_de_zero : (1 + k) * (1 - k) = 0 ∧ 1 + k ≠ 0 ∧ 1 - k ≠ 0
theorem plus_mul, minus_mul                       -- w₊ = z₁ − i z₂, w₋ = z₁ + i z₂ são multiplicativas
theorem divisor_iff : (∃ v ≠ 0, w * v = 0) ↔ plus w = 0 ∨ minus w = 0
noncomputable def zetaBC (w : BC) : BC           -- (ζ(w₊), ζ(w₋)) nas coordenadas idempotentes
theorem zetaBC_ofComplex : zetaBC ⟨s, 0⟩ = ⟨riemannZeta s, 0⟩
theorem zetaBC_eq_zero_iff : zetaBC w = 0 ↔ riemannZeta (plus w) = 0 ∧ riemannZeta (minus w) = 0
theorem zetaBC_divisor_iff : (∃ v ≠ 0, zetaBC w * v = 0) ↔ riemannZeta (plus w) = 0 ∨ riemannZeta (minus w) = 0
theorem target_iff_RHbc : Target ↔ RHbc
theorem re_altura_complexa : Re(σ + i (a + i b)) = σ − b
```

**O que é**: a álgebra exata do "segundo universo `j`". Com `k = i j` vale `k² = +1` e há divisores de zero, mas a
decomposição idempotente `w ↦ (z₁ − i z₂, z₁ + i z₂)` transforma `BC` em duas cópias de `ℂ`. Por isso todo zero da
extensão bicomplexa de ζ é um **par de zeros complexos**, e todo valor "divisor de zero" vem de um zero complexo
comum numa das coordenadas: o segundo universo **não cria nem esconde** zeros, e a RH bicomplexa equivale à RH. O
deslocamento `σ_ef = σ − b` acontece dentro de `ℂ` com uma altura complexa `t = a + i b`.

**O que NÃO é**: não é progresso em RH; mostra que estender o domínio para `j` não muda o problema.
**Origem**: novo neste repositório. **Axiomas**: `[propext, Classical.choice, Quot.sound]` (fixados em
`ClayRiemannProof/Audit.lean`).

## 7. As "travas" de Euler: o que é teorema e o que não é

Arquivo: `ClayRiemannProof/Locks.lean`.

```lean
theorem target_iff_desvio_zero : Target ↔ ∀ ρ, ζ ρ = 0 → (não trivial) → ρ ≠ 1 → ρ.re - 1/2 = 0   -- "b = 0"
theorem trava1_algebra (hp : 1 < p) : p ^ (-σ) = p ^ (-(1 - σ)) ↔ σ = 1/2
theorem ponte_vale_em_todo_sigma (s : ℂ) : completedRiemannZeta (1 - s) = completedRiemannZeta s
theorem ponte_em_sete_decimos (t : ℝ) : Λ(0,3 − it) = Λ(0,7 + it)
theorem simetria_nao_basta : ∃ G, (∀ s, G (1 - s) = G s) ∧ G (1/4) = 0 ∧ G (3/4) = 0 ∧ (1/4 : ℂ).re ≠ 1/2
theorem trava2_complexo : (1 + I) * (1 - I) = 2
theorem zeta_tem_zeros_em_C : riemannZeta (-2) = 0
theorem euler_trava (h : 1 ≤ s.re) : riemannZeta s ≠ 0
theorem retangulo (hρ : ρ ∈ Z) : torcao ρ ∈ Z ∧ espelho ρ ∈ Z
```

**O que é**: separa, no kernel, o que é verdadeiro nas duas "travas" propostas. A igualdade `p^{−σ} = p^{−(1−σ)}`
só vale em `σ = ½`, mas isso **não** restringe os zeros: a equação funcional vale em todo `σ`, inclusive `0,7`, e
uma função simétrica pode ter zeros fora de `½`. `ℂ` não ter divisores de zero também não impede zeros (`ζ(−2) = 0`).
A trava efetiva do produto de Euler é `ζ(s) ≠ 0` para `Re s ≥ 1`.

**O que NÃO é**: não é prova nem refutação de RH; mostra que as duas "travas" não implicam RH.
**Origem**: novo neste repositório. **Axiomas**: `[propext, Classical.choice, Quot.sound]`.

## 8. Pontes, nós, leis, operadores, vetores e tensões

Arquivo: `ClayRiemannProof/Bridges.lean`.

```lean
-- vetor de desvio δ(s) = (b, t) = (Re s − ½, Im s) e os operadores de Klein como trocas de sinal
theorem delta_tensao (s) : delta (tensao s) = -delta s                          -- (−b, −t)
theorem delta_espelho (s) : delta (espelho s) = ((delta s).1, -(delta s).2)      -- (b, −t)
theorem delta_torcao (s) : delta (torcao s) = (-(delta s).1, (delta s).2)        -- (−b, t)
theorem delta_compressao (l s) : delta (compressao l s) = l • delta s
-- leis do quarteto (incondicionais)
theorem baricentro (s) : (s + espelho s + tensao s + torcao s) / 4 = 1 / 2
theorem tensoes_cancelam (s) : b(s) + b(s̄) + b(1 − s) + b(1 − s̄) = 0
theorem energia_eq (s) : energia s = 4 * (s.re - 1 / 2) ^ 2
theorem energia_lt_um (hs : s ∈ Z) : energia s < 1
theorem vetor_de_zero (hs : s ∈ Z) : |b| < 1 / 2 ∧ 13 < |t|
-- o nó: a órbita de Klein de um zero
theorem card_orbita_reta (hs : s ∈ Z) (h : s.re = 1 / 2) : (orbita s).card = 2
theorem card_orbita_fora (hs : s ∈ Z) (h : s.re ≠ 1 / 2) : (orbita s).card = 4
theorem target_iff_nos_desfeitos : Target ↔ ∀ s ∈ Z, (orbita s).card = 2
theorem not_target_iff_no : ¬ Target ↔ ∃ s ∈ Z, (orbita s).card = 4
-- parâmetro espectral λ = s(1 − s) (Selberg) e ordenada γ = −i(s − ½)
theorem lam_im (s) : (lam s).im = -2 * (s.re - 1 / 2) * s.im                    -- Im λ = −2bt
theorem lam_na_reta (h : s.re = 1 / 2) : lam s = 1/4 + t²
theorem target_iff_lam_real : Target ↔ ∀ s ∈ Z, (lam s).im = 0
theorem lam_re_gt (hs : s ∈ Z) : 169 < (lam s).re
theorem target_iff_gam_real : Target ↔ ∀ s ∈ Z, (gam s).im = 0
theorem hilbert_polya (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric)
    (h : ∀ s ∈ Z, HasEigenvalue T (gam s)) : Target
-- a ponte única
theorem pontes : List.TFAE [Target, Gap, D_ω infinitesimal, ∀ M, RHnoMundo M, RHbc, b = 0,
    sem zeros em ½ < Re s < 1, ∀ a > ½, FimLivre a, torção fixa os zeros, energia 0, nós desfeitos,
    λ real, γ real]
```

**O que é**: a camada de operadores, vetores e tensões sobre os zeros, e a reunião das treze formulações do
repositório num único `List.TFAE`. São incondicionais o baricentro, o cancelamento das tensões, a energia `< 1`, o
vetor de todo zero em `(−½, ½) × {|t| > 13}` e `Re λ > 169`. `hilbert_polya` é a forma exata da ponte de
Hilbert–Pólya: os autovalores de um operador simétrico são reais.

**O que NÃO é**: `pontes` mostra que as treze formulações são a mesma proposição. Nenhuma é mais fraca, e provar
qualquer uma é provar RH. `hilbert_polya` não constrói operador nenhum. Não é prova de RH.
**Origem**: novo neste repositório. **Axiomas**: `[propext, Classical.choice, Quot.sound]` (28 guardas).

## 9. Identidade de Nyman–Beurling para `θ` real (teorema)

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
`∫_0^1 {θ/x} x^{s−1} dx` sozinha (sem o termo `θ{1/x}`) tem também o termo `θ/(s−1)` (observação,
não formalizada aqui).

**Origem**: escrito neste repositório.

**Axiomas**: `[propext, Classical.choice, Quot.sound]` (14 declarações; ver `Audit.lean`).

## 10. As três travas juntas: o que seguram e o que não seguram (teorema)

Arquivo: `ClayRiemannProof/TresTravas.lean`.

```lean
structure Travas (F : ℂ → ℂ) : Prop where
  inteira : Differentiable ℂ F
  ponte : ∀ s, F (1 - s) = F s                                  -- ξ(s) = ξ(1 − s)
  conjugacao : ∀ s, F (conj s) = conj (F s)                      -- ζ(s̄) = conj ζ(s)
  euler : ∀ s : ℂ, 1 ≤ s.re → F s ≠ 0                            -- o que o produto de Euler dá

theorem zeta_tem_as_tres : (∀ s, Λ (1 - s) = Λ s) ∧ (∀ s, ζ (conj s) = conj (ζ s)) ∧ (∀ s, 1 ≤ Re s → ζ s ≠ 0)
theorem quarteto (hF : Travas F) (h : F ρ = 0) : F (1 - ρ) = 0 ∧ F (conj ρ) = 0 ∧ F (1 - conj ρ) = 0
theorem tres_travas_nao_bastam :
    ∃ F, Travas F ∧ (∀ a b : ℂ, a * b = 0 → a = 0 ∨ b = 0) ∧ ∃ ρ, F ρ = 0 ∧ 0 < Re ρ < 1 ∧ Re ρ ≠ 1/2
theorem retangulo_nao_colapsa : G (1 − ¼) = 0 ∧ Re (1 − ¼) = ¾        -- G(s) = (s − ¼)(s − ¾)
theorem travas_independentes   -- s − ¾: sem a ponte; (s − 3/2)(s + ½): sem Euler; i(s − ½): sem a conjugação
```

**O que é**: a proposta "precisa das três travas juntas (a ponte `ξ(s) = ξ(1 − s)`, a conjugação e a trava de Euler,
com `ℂ` sem divisores de zero) para segurar ½" separada em duas partes. A parte *necessária* vale no sentido fraco
dos exemplos: tirar uma trava solta um zero da reta (Davenport–Heilbronn sem Euler; `ζ(s) + ζ(s + 1)` sem a ponte;
bicomplexos com `k² = 1` com divisores de zero), e no kernel as três são independentes entre si. A parte
*suficiente* é falsa para as três como propriedades: `G(s) = (s − ¼)(s − ¾)` é inteira, tem as três e se anula em
`¼` e `¾`; as travas dobram o zero no retângulo, não o levam para a reta.

**O que NÃO é**: não refuta RH e não é um passo para ela. Davenport–Heilbronn, Epstein com `h > 1` e
`ζ(s) + ζ(s + 1)` são resultados sobre outras funções, numéricos ou de contagem, e não estão no kernel. O que
falta para segurar ½ não é uma quarta propriedade desse tipo: é a própria hipótese de Riemann. `OPEN_MATH = true`.

**Origem**: novo neste repositório (resposta formal ao "ataque conjunto" dos quase-Riemann).

**Axiomas**: `[propext, Classical.choice, Quot.sound]` (20 guardas em `Audit.lean`).

## 11. O mesmo comportamento em outras áreas: o quarteto, o círculo e as duas saídas da linha

Arquivo: `ClayRiemannProof/Analogs.lean`.

```lean
-- lei abstrata do quarteto: f(−w) = f(w), f(w̄) = conj f(w)  ⟹  zeros em w, −w, w̄, −w̄
theorem quarteto_abstrato (hf : Simetrica f) (h : f w = 0) : f (-w) = 0 ∧ f (conj w) = 0 ∧ f (-conj w) = 0
theorem xi_simetrica : Simetrica (fun w => completedRiemannZeta (1 / 2 + w))
theorem simetria_nao_basta_abstrata : ∃ f, Simetrica f ∧ f (1/4 + I) = 0 ∧ (1/4 + I).re ≠ 0
-- lei universal do círculo (Ihara–Ramanujan; Lee–Yang com q = 1)
theorem ihara_ramanujan (hq : 0 < q) (hu : 1 - λ u + q u² = 0) : q * normSq u = 1 ↔ λ ^ 2 ≤ 4 * q
theorem ihara_fora_real (hq : 0 < q) (hu : …) (h : 4 * q < λ ^ 2) : u.im = 0
theorem ihara_quarteto (hq : 0 < q) (hu : …) : ū e 1/(q u) também são raízes
theorem circulo_iff_reta (hL : L ≠ 0) (s) : e^L * normSq (exp (−L s)) = 1 ↔ s.re = 1 / 2
theorem lee_yang_ferro (hβ : 0 < β) (hz : z² + 2 e^{−2βJ} z + 1 = 0) : normSq z = 1 ↔ 0 ≤ J
-- as duas saídas da linha
theorem lam_real_iff (s) : (lam s).im = 0 ↔ s.re = 1 / 2 ∨ s.im = 0
theorem linha_iff_quarto (h : (lam s).im = 0) : s.re = 1 / 2 ↔ 1 / 4 ≤ (lam s).re      -- λ ≥ ¼ de Selberg
theorem excepcional (h1 : 1/2 < σ) (h2 : σ < 1) : (lam σ).im = 0 ∧ 0 < (lam σ).re ∧ (lam σ).re < 1/4
theorem zeta_sem_saida_real (hs : s ∈ Z) : s.im ≠ 0
theorem selberg_polya (T : E →ₗ[ℂ] E) (hT : T.IsSymmetric) (h : ∀ s ∈ Z, HasEigenvalue T (lam s)) : Target
```

**O que é**: a parte matemática dos análogos entre áreas.
- A lei do quarteto vale para a zeta completada (`xi_simetrica`), para a partição da QCD em `μ̂` e para os
  espectros hamiltonianos. Ela não segura os zeros na linha.
- Uma única lei quadrática dá a cota de Ramanujan dos grafos e o círculo de Lee–Yang para dois spins: no círculo ⟺
  ferromagnético. Fora do círculo, as raízes são reais.
- Com `λ = s(1 − s)` real (sistema autoadjunto), um zero só sai da reta pelo eixo real: os autovalores excepcionais
  de Selberg e os grafos não Ramanujan. Para ζ essa saída está fechada no kernel (`ζ(σ) < 0` em `(0, 1)`), por isso
  `selberg_polya` basta para o enunciado do Clay.

Verificação numérica (fora do kernel): o fulereno C60 é Ramanujan (`|λ| ≤ 2,7566 < 2√2`), então todos os zeros
de Ihara dele estão em `Re s = ½`. A escada `C_n × K_2` deixa de ser Ramanujan para `n` ímpar `≥ 9` e para todo
`n ≥ 15`, com zeros reais fora da linha (`n = 20`: `s = 0,8286` e `0,1714`).

**O que NÃO é**: nenhum desses sistemas tem zeros de ζ; o que se transfere é a geometria e o mecanismo.
`selberg_polya` não constrói operador nenhum. Não é prova de RH.
**Origem**: novo neste repositório. **Axiomas**: `[propext, Classical.choice, Quot.sound]` (16 guardas).

## 12. A fronteira: Hadamard, Li, de Bruijn–Newman e o objeto desejado (enunciados + implicações provadas)

Arquivos: `ClayRiemannProof/Fronteira/Hadamard.lean`, `Li.lean`, `Ht.lean`, `Clay.lean`.

```lean
def xi (s : ℂ) : ℂ := (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2     -- ξ(s) = ½ s(s−1) π^{−s/2} Γ(s/2) ζ(s)
theorem xi_one_sub (s) : xi (1 - s) = xi s
theorem differentiable_xi : Differentiable ℂ xi
theorem xi_eq (h0 : s ≠ 0) (h1 : s ≠ 1) : xi s = s * (s - 1) / 2 * completedRiemannZeta s
def XiHadamard : Prop        -- ξ(s) = e^{A+Bs} ∏ (1 − s/ρ) e^{s/ρ}            (verdadeiro; falta na Mathlib)
def liCoeff (n : ℕ) : ℂ      -- λₙ = 1/(n−1)! · dⁿ/dsⁿ [s^{n−1} log ξ(s)] em s = 1
def CriterioDeLi : Prop      -- RH ⟺ ∀ n ≥ 1, λₙ ≥ 0                           (verdadeiro; não formalizado)
def PositividadeDeLi : Prop  -- ∀ n ≥ 1, λₙ ≥ 0                                 (aberto: é RH)
def H (t : ℝ) (z : ℂ) : ℂ    -- ∫₀^∞ e^{tu²} Φ(u) cos(zu) du
def deBruijnNewman : ℝ       -- inf {t | H_t só tem zeros reais}
def RodgersTao : Prop        -- 0 ≤ Λ                                           (Rodgers–Tao 2018; não formalizado)
def RH_iff_Lambda : Prop     -- RH ⟺ Λ ≤ 0                                      (de Bruijn, Newman; não formalizado)
def PlattTrudgianLambda : Prop -- Λ ≤ 0,2                                        (Platt–Trudgian 2021; não formalizado)
theorem clay_como_proposto_falso : ¬ ∀ ρ, riemannZeta ρ = 0 → ρ.re = 1 / 2      -- ζ(−2) = 0
theorem target_de_li (hLi : CriterioDeLi) (hPos : PositividadeDeLi) : Target
theorem target_de_dbn (h : RH_iff_Lambda) (hΛ : deBruijnNewman ≤ 0) : Target
```

**O que é**: o esqueleto até o objeto desejado, sem `sorry` e sem `axiom`. Os teoremas publicados que faltam na
Mathlib (Hadamard, Li, de Bruijn–Newman, Rodgers–Tao, Platt–Trudgian) ficam como `Prop` com definição de verdade
(`liCoeff`, `H`, `deBruijnNewman` não são marcadores); os dois caminhos ficam como implicações provadas, com as peças
abertas nos argumentos. O alvo proposto `∀ ρ, ζ ρ = 0 → Re ρ = ½` é falso por causa dos zeros triviais; o alvo certo é
`Target` (`RiemannHypothesis`).

**O que NÃO é**: nenhuma peça aberta foi provada. `PositividadeDeLi` e `Λ ≤ 0` são, cada uma, a hipótese de
Riemann. `OPEN_MATH = true`.
**Origem**: enunciados da literatura (Hadamard 1893; Li 1997; Bombieri–Lagarias 1999; de Bruijn 1950; Newman 1976;
Rodgers–Tao 2018; Platt–Trudgian 2021); `xi` e as implicações, novos. **Axiomas**: `[propext, Classical.choice,
Quot.sound]` (20 guardas).

## 13. Zeros de ζ acima de 3·10¹² (cálculo certificado fora do kernel)

Arquivos: `computations/zeros/zeros.c`, `computations/zeros/janelas.py`, `.github/workflows/zeros.yml`.

Platt e Trudgian (2021): até `T_PT = 3 000 175 332 800` há exatamente 12 363 153 437 138 zeros, todos em
`Re s = ½`. Um certificado de mais 20 000 zeros, até `g_b = 3 000 175 337 471,5`, foi citado em outubro de 2026; não o
localizamos, então a faixa `(T_PT, g_b]` é recalculada junto. A faixa nova pedida é `(g_b, g_b + 5000]`.

O workflow usa aritmética intervalar (FLINT 3 / Arb): `N(T)` exato em `T_PT`, `g_b` e `g_b + 5000` (contagem de
Turing) e todos os zeros de índice `N(T_PT) + 1 … N(g_b + 5000)` pelo método local de Platt, cada um como bola
`[t ± r]` com `Z(t) = 0` (em `Re s = ½`). Conferência: o número de zeros na reta em `(a, b]` tem que ser igual a
`N(b) − N(a)`, que conta todos os zeros de `0 < Re s < 1` nessas alturas; um zero fora da reta (com o par `1 − ρ̄` na
mesma altura) quebraria a igualdade. O resultado e a lista de zeros vão para a branch `resultados-zeros`.

**O que NÃO é**: prova. É a mesma verificação finita que o mundo fez até 3·10¹², levada um pouco além; nenhuma altura
finita fecha RH. Não entra no kernel do Lean.

**Estado em 2/11/2026**: a execução `41542819161` do workflow falhou antes de gravar zeros. O `N(T_PT)` devolvido
(`12 362 403 019 661`) não bate com o publicado (`12 363 153 437 138`; `θ(T_PT)/π + 1 = 12 363 153 437 137,1`), e o
script quebrou ao ler esse número. A janela da seção 15 foi feita localmente com a mesma biblioteca e começa
exatamente no índice publicado.

## 14. O critério de Li sem Hadamard: a forma finita, `ξ` e o encontro reta–círculo (teorema)

Arquivos: `ClayRiemannProof/LiFinite.lean`, `ClayRiemannProof/Xi.lean`, `ClayRiemannProof/LiCircle.lean`.

```lean
-- a variável de Li w = 1 − 1/ρ leva a reta ao círculo (a mesma lei de Ihara e Lee–Yang)
theorem normSq_cayley_mul (h : ρ ≠ 0) : normSq (cayley ρ) * normSq ρ = normSq ρ - (2 * ρ.re - 1)
theorem norm_cayley_eq_one_iff (h : ρ ≠ 0) : ‖cayley ρ‖ = 1 ↔ ρ.re = 1 / 2
theorem one_lt_norm_cayley_iff (h : ρ ≠ 0) : 1 < ‖cayley ρ‖ ↔ ρ.re < 1 / 2
-- critério de Li finito (Bombieri–Lagarias): família finita de não nulos fechada por ρ ↦ 1 − ρ
theorem li_chave (hs : s.Nonempty) (hu : ∀ j ∈ s, ‖u j‖ = 1) (a) : ∃ n ≥ a, 1/8 ≤ ∑ j ∈ s, (u j ^ n).re
theorem li_finito (h0 : ∀ i, ρ i ≠ 0) (hsym : ∀ i, ∃ j, ρ j = 1 - ρ i) :
    (∀ i, (ρ i).re = 1 / 2) ↔ ∀ n, 0 ≤ (∑ i, (1 - (1 - 1 / ρ i) ^ n)).re
theorem li_no_mundo (hρ : Set.range ρ = {s | s ∈ Z ∧ |s.im| ≤ Zh}) : RHateZ Zh ↔ ∀ n, 0 ≤ (li ρ n).re
theorem li_detecta_fora_da_reta : (li ![1/4, 3/4] 2).re = -64 / 9
-- ξ e o primeiro coeficiente de Li pela definição por derivadas (sem zeros, sem Hadamard)
theorem xi_eq_zero_iff (s) : xi s = 0 ↔ s ∈ Z
theorem li_one_eq : li 1 = 1 + γ/2 − ½ log 4π                -- = 0,0230957…
theorem li_one_pos : (li 1).im = 0 ∧ 0 < (li 1).re
def HadamardXi : Prop ; def Li1997 : Prop                     -- enunciados corretos, hipóteses nomeadas
-- quarteto a quarteto
theorem li_quarteto (hz : z ≠ 0) : (∀ n, 0 ≤ liQ z n) ↔ ‖z‖ = 1
theorem target_iff_li_quartetos : Target ↔ ∀ ρ ∈ Z, ∀ n, 0 ≤ liQ (mob ρ) n
theorem target_iff_ramanujan : Target ↔ ∀ ρ ∈ Z, ∃ c : ℝ, c ^ 2 ≤ 4 ∧ 1 − c·mob ρ + mob ρ² = 0
theorem encontro : List.TFAE [Target, ξ, círculo, Li por quartetos, Ramanujan]
```

**O que é**: a frente da positividade levada ao kernel sem o produto de Hadamard.
- `li_finito` é o critério de Li para qualquer família **finita** simétrica de zeros, provado só com somas
  geométricas e um argumento de média. Fora da reta, a simetria dá um `|w| > 1`, e as potências desse `w` acabam
  tornando algum `λ_n` negativo; `li_detecta_fora_da_reta` mostra isso para `{¼, ¾}`.
- `li_no_mundo` liga o critério aos mundos finitos: RH até a altura `Z` ⟺ positividade de Li dos zeros até `Z`.
- `encontro` liga Li, o círculo de Ihara–Ramanujan e Lee–Yang, e `ξ`.
- `Xi.xi` é a mesma definição de `Fronteira.Hadamard.xi`, em outro espaço de nomes.

**O que NÃO é**: o critério de Li verdadeiro soma sobre **todos** os zeros de ζ; ligar essa soma aos `λ_n` por
derivadas exige o produto de Hadamard (`HadamardXi`), ainda não provado. Não prova RH. `OPEN_MATH = true`.
**Origem**: Li (1997), Bombieri–Lagarias (1999); formalização nova. **Axiomas**: `[propext, Classical.choice,
Quot.sound]` (55 guardas).

## 15. A lógica de Turing no kernel e uma janela certificada acima de Platt–Trudgian

Arquivos: `ClayRiemannProof/Turing.lean`, `computations/zeros/janelaA/`.

```lean
theorem zero_em_aberto : hardyZ a * hardyZ b < 0 → ∃ x ∈ Ioo a b, hardyZ x = 0   -- troca de sinal ⟹ zero na reta
theorem trocas_de_sinal (ht : StrictMono t) (hs : ∀ i, Z(tᵢ) Z(tᵢ₊₁) < 0) : ∃ L, L.card = k ∧ … hardyZ x = 0
theorem turing_logica (hN : (Janela T₁ T₂).encard ≤ k) (hLk : L.card = k) (hL : … hardyZ x = 0) : JanelaNaReta T₁ T₂
theorem turing_janela … : JanelaNaReta T₁ T₂
theorem janelas_colam (h12 : JanelaNaReta T₁ T₂) (h23 : JanelaNaReta T₂ T₃) : JanelaNaReta T₁ T₃
theorem rhateZ_estende (h0 : RHateZ Z₀) (hJ : JanelaNaReta Z₀ Z₁) : RHateZ Z₁
```

**O que é**: as duas metades de toda verificação de RH até uma altura, provadas no kernel. Uma troca de sinal de `Z`
dá um zero na reta. Se a janela tem no máximo `k` zeros, contando todos os `σ`, e há `k` zeros na reta dentro dela,
então todos os zeros da janela estão na reta. As janelas colam e estendem os mundos finitos.

A janela `janelaA` (FLINT 3.6.0, `acb_dirichlet_platt_hardy_z_zeros`, 216 bits, 110 s) traz os 5000 zeros de
índice `12 363 153 437 138` a `12 363 153 442 137`, de `t = 3 000 175 332 799,93…` a `t = 3 000 175 333 968,18…`, como
bolas da Arb. A função só devolve um bloco depois de fixar o índice pela contagem de Turing, então os 4 999 zeros
acima de `T_PT` nessa faixa estão na reta e são simples, segundo a garantia da Arb.

**O que NÃO é**: os números da janela vêm de fora do kernel; ligar `janelaA` a `rhateZ_estende` exigiria a
contagem `N(T)` e os sinais de `Z` provados no Lean. Nenhuma altura finita fecha RH. `OPEN_MATH = true`.
**Origem**: Turing (1953), Platt (2017), FLINT/Arb; formalização nova. **Axiomas**: `[propext, Classical.choice,
Quot.sound]` (11 guardas).

## Autor

Tiago Paschoalatto Fagliari (ShantiDraconis) — ORCID [0009-0006-6874-3910](https://orcid.org/0009-0006-6874-3910).
Como citar: `CITATION.cff`.
