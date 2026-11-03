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
de `#print axioms` de cada uma das 783 declarações públicas acrescentadas; `ClayRiemannProof/AuditThirteen.lean`
faz o mesmo para as 253 da cadeia certificada até a altura 13 (1 036 guardas no total). Todas dependem apenas de
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

**Resultado** (execução 41546782883, 983 s, FLINT 3.0.1, precisão de 256 bits):

| altura `T` | `N(T)` exato |
|---|---|
| `T_PT = 3 000 175 332 800` | 12 363 153 437 138 (igual ao publicado por Platt–Trudgian) |
| `g_b = 3 000 175 337 471,5` | 12 363 153 457 130 |
| `g_b + 5000 = 3 000 175 342 471,5` | 12 363 153 478 531 |

- `(T_PT, g_b]`: 19 992 zeros, todos em `Re s = ½`; igual a `N(g_b) − N(T_PT)`.
- `(g_b, g_b + 5000]`: **21 401 zeros, todos em `Re s = ½`**; igual a `N(g_b + 5000) − N(g_b)`. Primeiro
  `t = 3 000 175 337 471,501016502…`, último `t = 3 000 175 342 471,339274324…`.
- As 41 393 bolas são disjuntas e estão em ordem (maior raio `5,01·10⁻¹⁸`). O par mais próximo — onde um par de zeros
  sairia da reta, se saísse — são os zeros 12 363 153 465 694 e 12 363 153 465 695, em
  `t ≈ 3 000 175 339 472,0499` e `3 000 175 339 472,0579` (distância `0,0080`): os dois estão na reta, separados.
- Conclusão: nenhum zero de ζ com `0 < Re s < 1`, `Re s ≠ ½` e `3 000 175 332 800 < Im s ≤ 3 000 175 342 471,5`.
  Com Platt–Trudgian: RH conferida (numericamente, com intervalos) até a altura `3 000 175 342 471,5`.
  A lista completa (índice, ordenada, raio) está em `zeros_faixa.csv.gz` na branch `resultados-zeros`.

**O que NÃO é**: prova. É a mesma verificação finita que o mundo fez até 3·10¹², levada um pouco além; nenhuma altura
finita fecha RH. Não entra no kernel do Lean.

**Sobre a execução `41542819161`**: ela calculou `N(3·10¹²) = 12 362 403 019 661` (a altura redonda `3·10¹²`, não
`T_PT`) e quebrou ao ler o número, que a Arb imprime com casas decimais. As execuções seguintes calculam em `T_PT`, e
`N(T_PT) = 12 363 153 437 138` sai igual ao publicado. A janela `janelaA` da seção 15, feita à parte com a mesma
biblioteca, começa no índice `12 363 153 437 138` (`t = 3 000 175 332 799,93…`, logo abaixo de `T_PT`) e é coerente com
a lista acima, que começa no índice seguinte (`t = 3 000 175 332 800,2865…`).

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

## 16. Onde um zero sairia da reta primeiro: a lei da colisão, pares de Lehmer e a faixa permitida

Arquivos: `ClayRiemannProof/Colisao.lean`, `computations/lehmer/analise.py`, `computations/lehmer/analise.json`.

```lean
def H2 (a t : ℝ) (z : ℂ) : ℂ := z ^ 2 - (a : ℂ) ^ 2 - 2 * (t : ℂ)     -- um par isolado no fluxo de de Bruijn
theorem calor_t : HasDerivAt (fun s => H2 a s z) (-2) t                -- ∂ₜH = −2
theorem calor_z : deriv (deriv (fun w => H2 a t w)) z = 2              -- ∂²_z H = 2, logo ∂ₜH = −∂²_z H
theorem zeros_reais_iff : (∀ z, H2 a t z = 0 → z.im = 0) ↔ -(a ^ 2) / 2 ≤ t
theorem colisao : (∀ z, H2 (Δ / 2) t z = 0 → z.im = 0) ↔ -(Δ ^ 2) / 8 ≤ t   -- tempo de colisão −Δ²/8
theorem mais_proximo_sai_depois (h : |Δ₁| < |Δ₂|) : -(Δ₂ ^ 2) / 8 < -(Δ₁ ^ 2) / 8
theorem raiz_quadrada (ht : t ≤ -(a ^ 2) / 2) : H2 a t (I * √(2(−a²/2 − t))) = 0 ∧ … .im = √(2(−a²/2 − t))
```

**O mecanismo** (kernel): no fluxo do calor de de Bruijn, um zero só sai da reta colidindo com o vizinho; um par a
distância `Δ` colide em `t = −Δ²/8`. Para `ζ`, o critério de Csordas–Smith–Varga acrescenta os vizinhos
(`g = Σ 1/(x_k − x_j)² + 1/(x_{k+1} − x_j)²`, com `x = 2γ`): um par com `Δ²g < 4/5` (par de Lehmer) dá
`Λ ≥ λ = ((1 − (5/4)Δ²g)^{4/5} − 1)/(8g)`, cujo termo principal é o `−Δ²/8` do modelo. O par com `λ` mais perto de 0 é o
mais frágil. Rodgers–Tao (`Λ ≥ 0`) diz que esses `λ` chegam tão perto de 0 quanto se queira ("RH, se for verdade, é
verdade por pouco").

**Os pares mais frágeis da faixa certificada** (41 393 zeros, seção 13; `g` com os zeros da janela e a cauda pela
densidade — estimativa fora do kernel):

| índice | `γ_k` | `γ_{k+1} − γ_k` | espaçamento normalizado | `Δ²g` | `λ` (CSV) |
|---|---|---|---|---|---|
| 12 363 153 465 694 | 3 000 175 339 472,0499 | 0,007987 | 0,0342 | 0,0057 | −3,19·10⁻⁵ |
| 12 363 153 454 258 | 3 000 175 336 800,2785 | 0,009027 | 0,0386 | 0,0059 | −4,08·10⁻⁵ |
| 12 363 153 460 076 | 3 000 175 338 159,6114 | 0,009484 | 0,0406 | 0,0055 | −4,50·10⁻⁵ |
| 12 363 153 476 424 | 3 000 175 341 979,2703 | 0,010024 | 0,0429 | 0,0077 | −5,03·10⁻⁵ |
| 12 363 153 445 940 | 3 000 175 334 856,7921 | 0,011684 | 0,0500 | 0,0131 | −6,84·10⁻⁵ |

370 dos 400 menores intervalos são pares de Lehmer. Todos estão na reta (seção 13).

**A mesma lei em outra área** (matrizes aleatórias): os espaçamentos normalizados da faixa têm média 1,0000 e
variância 0,1756 (Wigner–GUE: 0,1781; Poisson: 1); a repulsão é cúbica (`P(s < 0,1)` observado `9,2·10⁻⁴`, GUE
`1,1·10⁻³`); o menor espaçamento, 0,0342, está na escala que o GUE prevê para 41 393 níveis (≈ 0,028). É a
estatística de autovalores de matrizes hermitianas aleatórias (Montgomery–Odlyzko), a mesma de espectros de
sistemas quânticos caóticos sem simetria de reversão temporal.

**A faixa onde um zero fora da reta ainda poderia estar**, na altura `T ≈ 3·10¹²`: a região sem zeros de
Mossinghoff–Trudgian–Yang (`σ ≥ 1 − 1/(5,558691 log t)`) dá `0,006262 < β < 0,993738`; abaixo de
`3 000 175 342 471,5` não há nenhum (seção 13). As estimativas de densidade `N(σ, T)` caem com `σ − ½`: se houvesse
zeros fora, a maior parte estaria perto da reta, num par de Lehmer forte, numa altura maior que a verificada.

**O que NÃO é**: nenhum desses números diz que existe zero fora da reta, nem onde; `λ < 0` em todos os pares, e
`Λ ≥ 0` já é teorema. O modelo de dois zeros é exato só para um par isolado. `OPEN_MATH = true`.
**Origem**: de Bruijn (1950), Newman (1976), Csordas–Smith–Varga (1994), Montgomery (1973), Odlyzko (1987),
Rodgers–Tao (2018), Mossinghoff–Trudgian–Yang (2022); a lei da colisão no kernel, nova. **Axiomas**:
`[propext, Classical.choice, Quot.sound]` (8 guardas).

## 17. Unicidade por simetria: verificar zeros na reta sem contar zeros (teorema)

Arquivo: `ClayRiemannProof/Verification.lean`.

```lean
theorem injetiva_de_derivada (hf : ∀ z ∈ ball c r, DifferentiableAt ℂ f z)
    (hd : ∀ z ∈ ball c r, ‖deriv f z - deriv f c‖ ≤ ε) (hε : ε < ‖deriv f c‖) : InjOn f (ball c r)
theorem torcao_mem_ball (hc : c.re = 1 / 2) (hz : z ∈ ball c r) : torcao z ∈ ball c r
theorem zero_na_bola_simetrica (hc : c.re = 1 / 2) (hinj : InjOn riemannZeta (ball c r))
    (hρ : ρ ∈ ball c r) (hz : ρ ∈ Z) : ρ.re = 1 / 2
theorem zero_unico_na_bola (hinj : InjOn riemannZeta (ball c r)) (hab : a ≤ b) (hs : hardyZ a * hardyZ b < 0)
    (hseg : ∀ t ∈ Icc a b, naReta t ∈ ball c r) :
    ∃ t ∈ Ioo a b, riemannZeta (naReta t) = 0 ∧ ∀ ρ ∈ ball c r, riemannZeta ρ = 0 → ρ = naReta t
theorem janelaNaReta_de_bolas (hc : centros na reta) (hinj : ζ injetiva em cada bola)
    (hcov : ∀ s ∈ Janela T₁ T₂, ∃ p ∈ B, s ∈ ball p.1 p.2) : JanelaNaReta T₁ T₂
theorem rhAteZ_de_bolas … : FiniteWorlds.RHateZ T
theorem logDeriv_completada (hs : 1 < s.re) :
    logDeriv completedRiemannZeta s = -L ↗Λ s - logDeriv (fun z => (Gammaℝ z)⁻¹) s
```

**O que é**: uma segunda rota para ligar uma janela calculada ao kernel. `Turing.turing_logica` precisa da cota
`(Janela T₁ T₂).encard ≤ k`, que vem do princípio do argumento para ζ (fora da Mathlib). Aqui a contagem não é
necessária:
- a torção `s ↦ 1 − s̄` leva cada bola centrada na reta nela mesma e leva zero em zero;
- numa bola onde ζ é injetiva, isso força todo zero a estar na reta;
- uma troca de sinal de `Z` dentro da bola dá a existência.

Os insumos são certificados numéricos finitos: a cota da derivada na bola e `|ζ| > 0` fora das bolas, do mesmo
tipo dos 930 que fecham a altura 13. `logDeriv_completada` é o lado dos primos da identidade em que as frentes se
encontram. O lado dos zeros, `Σ_ρ 1/(s − ρ)`, é o produto de Hadamard (seção 12, enunciado).

**O que NÃO é**: nenhuma bola concreta foi certificada no kernel ainda; nenhuma altura finita fecha RH.
`OPEN_MATH = true`.
**Origem**: argumento clássico de simetria; formalização nova. **Axiomas**: `[propext, Classical.choice,
Quot.sound]` (8 guardas).

## 18. A teia: a mesma colisão em todas as áreas e a escala em que um quarteto apareceria

Arquivos: `computations/alturas/alturas.py`, `.github/workflows/alturas.yml` (resultado na branch
`resultados-alturas`).

**A teia.** Em cada área há uma trava que segura os zeros (ou autovalores) numa reta ou num círculo, e só duas
saídas quando ela cai:

| área | trava | saída quando a trava cai | no kernel |
|---|---|---|---|
| curvas sobre corpos finitos | positividade (Weil, Deligne) | nenhuma: RH provada | — |
| grafos, química (Ihara) | `λ² ≤ 4q` (Ramanujan) | eixo real (escada `C_n × K₂`, `n = 20`: `s = 0,8286`) | `ihara_ramanujan`, `ihara_fora_real` |
| Lee–Yang | ferromagnetismo `J ≥ 0` | eixo real (antiferro) | `lee_yang_ferro` |
| Selberg | `λ ≥ ¼` | eixo real (autovalor excepcional) | `linha_iff_quarto`, `excepcional` |
| quântica PT, Krein, Hopf | PT não quebrada / assinatura definida | colisão de dois níveis → par complexo (ponto excepcional) | `raiz_quadrada` |
| fase linear FIR | nenhuma | quarteto `z, 1/z, z̄, 1/z̄` sempre | `quarteto_abstrato` |
| Davenport–Heilbronn, Epstein `h > 1` | sem produto de Euler | zeros fora da reta (DH: `0,8085 + 85,699i`) | `simetria_nao_basta_abstrata` |
| `ζ` | ? (é RH) | eixo real fechado (`zeta_sem_saida_real`); sobra a colisão | `colisao`, `quarteto_abstrato` |

Fechada a saída real, um zero de `ζ` só sairia da reta por **colisão de dois zeros vizinhos**, e a colisão tem a
mesma forma normal em todas as áreas: no limiar os dois se fundem, e depois saem perpendiculares à reta a uma
distância `√(2(t* − t))` (`raiz_quadrada`). Com a simetria `w ↦ −w` da equação funcional, o par vira o quarteto
`½ ± b ± iγ`.

**A escala.** O par mais frágil de uma janela de `N` zeros na altura `T` tem, pela repulsão do GUE e pela cota de
Csordas–Smith–Varga,

    λ ≈ −s_min² / (2ρ²),   ρ = log(T/2π)/2π,   s_min ≈ (9/(π²N))^{1/3}.

Na faixa da seção 13 (`N = 41 393`, `T ≈ 3·10¹²`) a fórmula com o `s_min` observado (0,0342) dá `−3,19·10⁻⁵`, igual
ao `λ` de Csordas–Smith–Varga do par 12 363 153 465 694. `λ` vai a 0⁻ como `N^{−2/3}(log T)^{−2}`: o tamanho da
varredura pesa mais que a altura. Previsão para as janelas do workflow:

| altura | `N` | `ρ` | `s_min` (GUE) | `λ` previsto |
|---|---|---|---|---|
| 10¹⁴ | 20 000 | 4,838 | 0,0357 | −2,7·10⁻⁵ |
| 10¹⁶ | 20 000 | 5,571 | 0,0357 | −2,1·10⁻⁵ |
| 10¹⁷ | 20 000 | 5,938 | 0,0357 | −1,8·10⁻⁵ |
| 10¹⁸ | 20 000 | 6,304 | 0,0357 | −1,6·10⁻⁵ |

**O primeiro run (41554617926) não certificou nenhuma janela.** Pedidos de 20 002 zeros numa só chamada, o método
local de Platt devolveu 8 048 (10¹⁴), 8 664 (10¹⁶) e 17 848 (10¹⁸), e a chamada de 10²⁰ não terminou em 4 h. O
custo de uma chamada cresce com a altura e quase não depende de quantos zeros se pedem: 157 s, 336 s e 4 906 s. Entre
10¹⁶ e 10¹⁸ isso é cerca de `T^{0,58}`, o que dá umas 19 h por chamada em 10²⁰. Por isso 10²⁰ e 10²² ficam fora do
alcance deste método num runner de 6 h (a fronteira, seção 23, varre essas alturas com blocos menores). O
`alturas.py` agora fica com os zeros que cada chamada devolveu e recomeça dali, e grava o estado depois de cada
chamada. O workflow roda uma tarefa por altura (10¹⁴, 10¹⁶, 10¹⁷, 10¹⁸) em paralelo e `junta.py` monta o
`alturas.json`.

**O segundo run (41588835957) certificou 10¹⁴, 10¹⁶ e 10¹⁷.** Em cada uma, 20 000 zeros consecutivos todos na reta.
O índice do primeiro zero confere com `N(T_a)`, `N(T_b) − N(T_a) = 20 000` pela contagem de Turing intervalar
(contagem fechando: nenhum zero fora da reta em `T_a < Im s ≤ T_b`), e as bolas são disjuntas. Resultado na branch
`resultados-alturas` (`alturas.json`, `alturas_1eXX.json`, `zeros_1eXX.csv.gz`):

| altura | `T_a` | `N(T_a)` | `N(T_b)` | maior raio | `s_min` (GUE: 0,0357) | var. de `s` (GUE: 0,1781) | `λ` do par mais frágil | previsto | zeros / contagem (s) |
|---|---|---|---|---|---|---|---|---|---|
| 10¹⁴ | 99 999 999 999 999,53 | 467 888 702 914 981 | …934 981 | 7,6·10⁻³ | 0,0323 | 0,1797 | −2,23·10⁻⁵ | −2,7·10⁻⁵ | 731 / 89 |
| 10¹⁶ | 9 999 999 999 999 999,67 | 54 118 226 280 292 476 | …312 476 | 6,2·10⁻³ | **0,0078** | 0,1761 | **−9,73·10⁻⁷** | −2,1·10⁻⁵ | 1 299 / 1 116 |
| 10¹⁷ | 99 999 999 999 999 999,67 | 577 829 042 746 896 153 | …916 153 | 8,5·10⁻⁴ | 0,0401 | 0,1783 | −2,28·10⁻⁵ | −1,8·10⁻⁵ | 6 341 / 3 053 |
| 10¹⁸ | — | — | — | — | — | — | — | −1,6·10⁻⁵ | 10 891 / > 3 580 |

Em 10¹⁶ o par 54 118 226 280 296 885/886 está a 0,0013949 um do outro (`s = 0,0078`, um quinto do mínimo esperado
pelo GUE em 20 000 zeros). É o mais perto da colisão entre as três janelas e 21 vezes mais perto de `0⁻` que a
previsão. Mesmo assim fica 2 vezes mais longe que o par da continuação em 3·10¹² (`−4,59·10⁻⁷`, em 2 milhões de
zeros). As variâncias dos espaçamentos ficam a 1% da de Wigner (GUE) nas três alturas. Em 10¹⁸ a Arb achou os
20 002 zeros (em 10 891 s), mas a contagem de Turing em `T_b` passou do limite de 3 580 s por chamada; sem ela a
janela não fecha, e a lista não foi gravada. As faixas de `λ` dos três pares, com as bolas da Arb como hipótese,
estão em `ClayRiemannProof/Alturas.lean` (no kernel, com as bolas como hipótese).

**A faixa provável, se existisse um quarteto**: altura além da verificada; no par de menor `s` de uma varredura
grande (é lá que `λ` chega mais perto de 0); com `β − ½` pequeno, porque logo depois do limiar o afastamento é
`√(2(t* − t))`. Cada janela do workflow certifica a contagem (`N(T_b) − N(T_a) = N`) e lista os pares mais frágeis.

**O que NÃO é**: a fórmula de escala é heurística (GUE + o termo principal de CSV), não teorema; ela diz onde olhar,
não que exista algo. `λ < 0` em todos os pares medidos e `Λ ≥ 0` é teorema. `OPEN_MATH = true`.
**Origem**: Csordas–Smith–Varga (1994), Montgomery (1973), Odlyzko (1987), Rodgers–Tao (2018); a tabela da teia junta
resultados clássicos de cada área; a lei da raiz quadrada no kernel, nova.

## 19. Álgebra bicomplexa de coordenadas, ponte condicional e coordenada centrada (suplementar; não prova RH)

Arquivos: `ClayRiemannProof/BicomplexCoordinates.lean`, `ClayRiemannProof/BicomplexConditional.lean`,
`ClayRiemannProof/CenteredStabilityBridge.lean`; notas de escopo em `BICOMPLEX_SCOPE.md` e `CROSS_DOMAIN_SCOPE.md`
(branch `bicomplex-coordinate-algebra`, trazida ao `main`).

O módulo formaliza identidades de coordenadas: `i²=j²=-1`, `ij=ji=k`, `k²=1`,
`(1+k)(1-k)=0` com fatores não nulos, o inverso de `j`, e as contas de
`-1+i(a+ib)` versus `-1+i(a+jb)`. Também verifica que as coordenadas reais
dos componentes idempotentes são `σ+b` e `σ-b`, ambas iguais a `σ` quando `b=0`.

Aqui `a+ib` usa a unidade complexa ordinária: `-1+i(a+ib)=(-1-b)+ia`; isso não requer
uma extensão bicomplexa. Com uma unidade independente `j`, `i(a+jb)=ia+kb`, e o
coeficiente escalar real não muda. Zero-divisores são elementos não nulos cujo produto
pode ser zero; isso não torna um valor de função igual a zero quando apenas um componente
idempotente se anula.

Esta seção não define `ζ` sobre os bicomplexos e não implica que os zeros da zeta clássica
estejam ou não na linha crítica. A Hipótese de Riemann continua aberta neste repositório.

Os outros dois módulos da branch:
- `BicomplexConditional.both_components_RH_force_center`: se as duas componentes `σ ± b + it` são zeros na faixa e
  RH vale para elas, então `σ = ½` e `b = 0`. Uma componente sozinha não força `b = 0`.
- `CenteredStabilityBridge.riemann_iff_centered_neutral`: RH ⟺ todo zero não trivial tem `Re(ρ − ½) = 0`. Entra
  na ponte total da seção 21.

O zero de Epstein citado em `CROSS_DOMAIN_SCOPE.md`, para `m² + 5n²`, foi conferido numericamente (fora do kernel).
Com `Z_Q(s) = ζ(s)L(s, χ₋₂₀) + L(s, χ₋₄)L(s, χ₅)`, fórmula que confere com a soma direta em `s = 2`, o zero refinado é
`0,932969697485414 + 15,668249531278472i`, com `|Z_Q| ≈ 10⁻³¹`. O espelho `0,067030302514586 + 15,668…i` também é
zero.

**Axiomas**: 34 guardas. As identidades por `decide` em `BicomplexCoordinates` não dependem de axioma nenhum ou só
de `propext`; as demais usam `[propext, Classical.choice, Quot.sound]`.

## 20. Se existir zero fora da reta, existe um de altura mínima (teorema condicional)

Arquivo: `ClayRiemannProof/PrimeiroFora.lean`.

```lean
theorem zeros_isolados (hz : z ≠ 1) : ∀ᶠ w in 𝓝[≠] z, riemannZeta w ≠ 0
theorem zeros_finitos (T : ℝ) : ((Icc 0 1 ×ℂ Icc 1 T) ∩ riemannZeta ⁻¹' {0}).Finite
theorem primeiro_fora (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) :
    ∃ ρ ∈ Z, ρ.re ≠ 1 / 2 ∧ 0 < ρ.im ∧ ∀ σ ∈ Z, σ.re ≠ 1 / 2 → ρ.im ≤ |σ.im|
theorem primeiro_fora_acima (hW : RHateZ W) (h : ∃ ρ ∈ Z, ρ.re ≠ 1 / 2) : … (W : ℝ) < ρ.im …
theorem primeiro_fora_acima_13 (h : …) : … 13 < ρ.im …                                   -- sem hipótese
def JanelaArb2026 : Prop := Turing.JanelaNaReta 3000175332800 3000175342471             -- seção 13, hipótese nomeada
theorem rhAteZ_janela (hPT : PlattTrudgian2021) (hJ : JanelaArb2026) : RHateZ 3000175342471
theorem primeiro_fora_acima_janela (hPT) (hJ) (h : …) : … 3000175342471 < ρ.im …
```

**O que é**: o enunciado **condicional**. Se existe um zero não trivial fora da reta, existe um de altura mínima. A
prova:
- ζ é analítica em `ℂ ∖ {1}`, que é conexo, e não é identicamente nula; pelo princípio da identidade, seus zeros
  são isolados;
- num retângulo compacto, zeros isolados são finitos;
- até a altura de um zero fora da reta só há um número finito deles, logo o mínimo existe.

Com RH verificada até `W`, esse primeiro zero tem `Im > W`. Isso vale para `W = 13` sem hipótese, para
`W = 3 000 175 332 800` com Platt–Trudgian e para `W = 3 000 175 342 471` com a janela da seção 13.

**O que NÃO é**: não afirma que exista zero fora da reta. Isolamento e finitude não implicam existência; o teorema só
diz onde estaria o primeiro, se existir. `OPEN_MATH = true`.
**Origem**: argumento clássico (zeros isolados de funções analíticas); formalização nova. **Axiomas**:
`[propext, Classical.choice, Quot.sound]` (11 guardas).

## 21. A ponte total: as 22 formulações são a mesma proposição (teorema)

Arquivo: `ClayRiemannProof/PontesTotal.lean`.

```lean
theorem pontes_total : List.TFAE
  [Target, Gap, D_N → 0, D_ω infinitesimal, ∀ M, RHnoMundo M, RHbc, b = 0, sem zeros em ½ < Re s < 1,
   fins fechados livres, inícios fechados livres, torção fixa os zeros, compressão preserva Re,
   colares arbitrariamente finos, energia 0, nós desfeitos, λ real, γ real, coordenada centrada neutra,
   zeros de ξ na reta, 1 − 1/ρ no círculo, Li por quartetos, Ramanujan]
```

**O que é**: junta num único `List.TFAE` toda equivalência com o enunciado do Clay que existe no repositório:
`Bridges.pontes` (13), `LiCircle.encontro` (5), Báez-Duarte na forma `D_N → 0`, os inícios fechados, a compressão,
os colares e a coordenada centrada da seção 19.

**O que NÃO é**: as 22 são a mesma proposição; provar qualquer uma é provar RH, e nenhuma é mais fraca.
`OPEN_MATH = true`. **Axiomas**: `[propext, Classical.choice, Quot.sound]` (1 guarda).
## 22. Forçar o zero no quarteto

Arquivos: `ClayRiemannProof/QuartetoForcado.lean`, `computations/lehmer/forca.py`, `computations/lehmer/forca.json`.

```lean
def Q (γ₀ κ : ℝ) (w : ℂ) : ℂ := ((w - I * γ₀) ^ 2 + κ) * ((w + I * γ₀) ^ 2 + κ)   -- w = s − ½
theorem Q_simetrica : Simetrica (Q γ₀ κ)                     -- Q(−w) = Q(w), Q(w̄) = conj Q(w), como ξ
theorem Q_na_reta (hκ : 0 ≤ κ) : ∀ w, Q γ₀ κ w = 0 → w.re = 0
theorem Q_quarteto (hκ : κ < 0) : Q γ₀ κ (√(−κ) + iγ₀) = 0 ∧ Q γ₀ κ (−√(−κ) + iγ₀) = 0 ∧ … ∧ 0 < √(−κ)
theorem quarteto_forcado : (∀ w, Q γ₀ ((a² + 2t)/4) w = 0 → w.re = 0) ↔ -(a ^ 2) / 2 ≤ t
theorem Q_quarteto_abstrato (h : Q γ₀ κ w = 0) : Q γ₀ κ (-w) = 0 ∧ Q γ₀ κ (conj w) = 0 ∧ Q γ₀ κ (-conj w) = 0
```

**O que é**: em `ζ` o quarteto não se força (a função é fixa e, na faixa da seção 13, todos os zeros estão na reta).
Força-se na deformação de de Bruijn: abaixo do tempo de colisão `t_c` de um par, o par sai da reta, e as duas
simetrias de `ξ` o completam em quarteto `½ ± b ± iγ_c`, com `b = √(2(t_c − t))/2`. Pelo teorema de Rodgers–Tao
(`Λ ≥ 0`), para todo `t < 0` a deformação `H_t` tem zeros fora da reta.

**O quarteto forçado nos pares mais frágeis da faixa certificada** (vizinhos congelados durante a colisão; `t_c`
coincide com o `λ` de Csordas–Smith–Varga até a quarta casa):

| par (índice) | centro `γ_c` | `t_c` | quarteto em `t = 2t_c`: `½ ± b ± iγ_c` |
|---|---|---|---|
| 12 363 153 465 694 | 3 000 175 339 472,05388 | −3,1927·10⁻⁵ | `b = 3,995·10⁻³` |
| 12 363 153 454 258 | 3 000 175 336 800,28301 | −4,0783·10⁻⁵ | `b = 4,516·10⁻³` |
| 12 363 153 460 076 | 3 000 175 338 159,61616 | −4,5018·10⁻⁵ | `b = 4,744·10⁻³` |

O primeiro quarteto que a deformação para trás cria nessa faixa nasce no par 12 363 153 465 694, em
`t = −3,1927·10⁻⁵`, com afastamento `b ∝ √(t_c − t)`: em `t = 2t_c` são os zeros `½ ± 0,003995 ± i·3 000 175 339 472,0539`
de `H_t` (não de `ζ`).

**O que NÃO é**: um zero de `ζ`. Em `t = 0` (a própria `ζ`) esse par está na reta, certificado. O modelo `Q` é exato;
os números da tabela são a dinâmica dos zeros com os vizinhos congelados (estimativa fora do kernel). `OPEN_MATH = true`.
**Origem**: de Bruijn (1950), Newman (1976), Csordas–Smith–Varga (1994), Rodgers–Tao (2018); o quarteto forçado no
kernel, novo. **Axiomas**: `[propext, Classical.choice, Quot.sound]` (7 guardas).

## 23. Onde o zero fora da reta estaria: a tendência de todas as varreduras e o ataque na escala escolhida

Arquivos: `computations/fronteira/varre.py`, `computations/fronteira/agrega.py`, `computations/ataque/ataque.py`,
`.github/workflows/fronteira.yml`, `.github/workflows/ataque.yml` (resultados nas branches `resultados-fronteira`,
`resultados-ataque` e `resultados-onda`).

**Comparar todos os números.** Cada varredura dá um ponto (altura `T`, zeros `N`, `s_min`, `λ` do par mais frágil,
zeros por segundo). Pela repulsão do GUE e pelo termo principal de Csordas–Smith–Varga,

    λ_min ≈ −½·(9/(π²N))^{2/3} / ρ²,   ρ = log(T/2π)/2π.

A curva vai a `0⁻` quando `N·ρ³` cresce e **não cruza 0 em nenhum `N` finito**. Por isso não existe uma altura em
que a tendência "aponte" o zero: se ele existir, aparece como quebra da tendência — um par com `λ ≥ 0` (já colidido
em `t = 0`) ou uma contagem de Turing que não fecha —, não como continuação da curva.

**A escala a atacar** é a que dá o maior `N·ρ³` por hora de cálculo; `ataque.py` mede os zeros por segundo em cada
altura e calcula onde concentrar a próxima onda. Zeros necessários para o par mais frágil chegar a cada `λ`:

| altura | `λ = −10⁻⁷` | `λ = −10⁻⁹` | recorde `−1,14541·10⁻¹¹` |
|---|---|---|---|
| 10¹³ | 1,1·10⁸ | 1,1·10¹¹ | 9,3·10¹³ |
| 10¹⁶ | 5,9·10⁷ | 5,9·10¹⁰ | 4,8·10¹³ |
| 10²⁰ | 2,9·10⁷ | 2,9·10¹⁰ | 2,4·10¹³ |
| 10²² | 2,2·10⁷ | 2,2·10¹⁰ | 1,8·10¹³ |

(O recorde de Saouter–Gourdon–Demichel veio de uma computação da ordem de 10¹³ zeros, na escala que a fórmula dá.)

**A primeira onda da fronteira (run 41557877448) quase não varreu.** O `varre.py` exigia exatamente 10 000 zeros
por chamada. O método local de Platt devolve menos que isso quando o pedido é grande (7 503 em 10¹³), a chamada contava
como falha e, depois de cinco falhas seguidas, a varredura parava. Em 10¹⁸ as chamadas vieram cheias: 28 200 pares em
5 h. Em 10²⁰ a 10²² uma chamada passa de 4 h (seção 18). O `varre.py` agora fica com os zeros que vieram e recomeça
dali. A matriz trocou 10²⁰ a 10²² por mais janelas em 10¹³ a 10¹⁸, onde o mérito `N·ρ³` por hora é maior. A melhor
medida até agora é a da continuação contígua (seção 26): 2 054 383 zeros em `T ≈ 3·10¹²`, par mais frágil com
`λ = −4,593·10⁻⁷`. A fórmula prevê `−1,6·10⁻⁶` para esse `N`; o par observado está 3,5 vezes mais perto de `0⁻`, dentro
da flutuação do mínimo de 2 milhões de espaçamentos.

**O que a primeira onda deu** (branch `resultados-fronteira`): 65 800 zeros, todos em 10¹⁸ (37 600 no deslocamento
0 e 28 200 no deslocamento 10¹²; as tarefas de 10¹³, 10¹⁴ e 10¹⁶ pararam no retorno parcial e as de 10²⁰–10²² foram
canceladas pelo tempo sem dados). O par mais frágil: zeros 6 144 758 226 908 699 989/…990, `γ ≈ 10¹⁸ + 3 899,320`,
intervalo 0,004024, `s = 0,0254` (GUE para 37 600 espaçamentos: 0,0290), `λ = −8,10·10⁻⁶` contra `−1,05·10⁻⁵` previsto.
No kernel, com as bolas da Arb (raio 2,4·10⁻³⁰) como hipótese: `−1,013·10⁻⁵ ≤ λ ≤ −8,09·10⁻⁶`
(`Continuacao.par_mais_fragil_1e18`). É 4 vezes mais perto de `0⁻` que o par da seção 13 e 18 vezes mais longe que o
da continuação (2 milhões de zeros): de novo, quem manda é `N`.

**Zeros por segundo medidos e a escala escolhida** (um job, método local de Platt; o mérito é `N·ρ³` por hora):

| altura | origem | zeros/s | `ρ` | mérito `N·ρ³`/h |
|---|---|---|---|---|
| 3·10¹² | continuação contígua (513 596 zeros por faixa) | 44,0 | 4,280 | 1,24·10⁷ |
| 10¹⁴ | alturas, run 41554617926 (8 048 zeros numa chamada) | 51,1 | 4,838 | **2,08·10⁷** |
| 10¹⁶ | idem (8 664 zeros) | 25,8 | 5,571 | 1,61·10⁷ |
| 10¹⁸ | idem (17 848 zeros) | 3,6 | 6,304 | 3,3·10⁶ |

A escala de maior mérito é 10¹⁴. A onda do ataque (`varre2.py`, com a mesma correção do retorno parcial) varre 16
janelas ali, com deslocamentos de 3·10¹² a 18·10¹² no índice, sem repetir as da fronteira.

**A 2ª onda da fronteira** (run 41591657623, `varre.py` corrigido): 7 791 406 zeros em 16 janelas de 10¹³ a 10¹⁸,
todos na reta. A tabela completa está em `RESUMO.md` da branch `resultados-fronteira`; a 1ª onda ficou em
`historico/run-41557877448/`. O par mais frágil são os zeros 467 888 702 979 044/…045 (`γ ≈ 10¹⁴ + 13 241,144`):
intervalo 0,0010522, `s = 0,0051` (o GUE espera 0,0123 para os 492 030 espaçamentos da janela),
`λ = −5,536·10⁻⁷`, contra `−3,22·10⁻⁶` previsto. No kernel, com as bolas da Arb (raio 7,8·10⁻²⁹) como hipótese,
`−6,93·10⁻⁷ ≤ λ ≤ −5,53·10⁻⁷` (`Continuacao.par_mais_fragil_onda2`). O 2º e o 3º pares vêm de 10¹⁶ (−7,79·10⁻⁷, e o par 54 118 226 280 296 885/886 da seção 18, −9,73·10⁻⁷).

| conjunto | zeros | `λ` do par mais frágil |
|---|---|---|
| seção 13 (3·10¹²) | 41 393 | −3,19·10⁻⁵ |
| fronteira, 1ª onda (10¹⁸) | 65 800 | −8,10·10⁻⁶ |
| alturas, 10¹⁶ (seção 18) | 20 000 | −9,73·10⁻⁷ |
| **fronteira, 2ª onda (10¹⁴)** | **7 791 406** | **−5,54·10⁻⁷** |
| continuação (3·10¹²) | 2 054 383 | −4,59·10⁻⁷ |
| recorde publicado (Saouter–Gourdon–Demichel 2011) | ≈ 10¹³ | −1,14541·10⁻¹¹ |

Com 3,8 vezes mais zeros que a continuação, a 2ª onda não passou dela (−5,54 contra −4,59·10⁻⁷). O mínimo de cada
varredura flutua muito em torno da lei de escala: na janela de 10¹⁴ ele ficou 6 vezes mais perto de `0⁻` que a
previsão; na de 10¹⁷, no deslocamento 10¹², 1,9 vez mais longe.

**A onda em 10¹⁴** (run 41594905434, `varre2.py`): 16 janelas com deslocamentos de 3·10¹² a 18·10¹² no índice, 8 661 651
zeros, todos na reta, contagem sem nenhum zero fora da reta em cada janela. Ela teve 1 109 violações da regra de
Rosser, 21,6% de pontos de Gram ruins e `S` entre −2,35 e +2,43 (5,8 desvios). O par mais frágil são os zeros
472 888 703 009 302/…303 (`γ ≈ 1,0103·10¹⁴`): intervalo 0,0012132, `s = 0,0059` (GUE: 0,0121), `λ = −7,36·10⁻⁷`
contra `−3,13·10⁻⁶` previsto. No kernel, com as bolas da Arb (raio 6,9·10⁻²⁸): `−9,20·10⁻⁷ ≤ λ ≤ −7,35·10⁻⁷`
(`Continuacao.par_mais_fragil_onda_1e14`). Somando a onda e a 2ª onda da fronteira,
foram 16,5 milhões de zeros em 10¹³–10¹⁸ sem nenhum fora da reta. O par mais perto de `0⁻` continua sendo o da
continuação (−4,59·10⁻⁷), seguido do de 10¹⁴ da fronteira (−5,54·10⁻⁷) e do desta onda (−7,36·10⁻⁷). O recorde
publicado, −1,14541·10⁻¹¹, veio de cerca de 10¹³ zeros: pela lei de escala, chegar perto dele pede da ordem de 10⁶
vezes mais zeros do que os varridos aqui. O ataque local desse run foi cortado pelo tempo (cancelado depois de 5 h).

**O ataque local**: para cada par mais frágil, `N(T)` exato nos pontos médios antes e depois do par;
`N(T_b) − N(T_a) = 2` quer dizer que os dois zeros da reta são os únicos zeros de `ζ` em `0 < Re s < 1` naquela faixa
de alturas — nenhum quarteto escondido no lugar mais provável.

**O que NÃO é**: a fórmula é heurística (GUE + CSV); o ataque é cálculo finito fora do kernel. `OPEN_MATH = true`.

## 24. Todas as quebras de tendência (Gram, Rosser, `S(t)`, extremos, `λ ≥ 0`)

Arquivos: `computations/quebras/quebras.py`, `computations/quebras/resumo.py`, `computations/ataque/varre2.py`,
`computations/quebras/resultados/` (e `QUEBRAS.md` nas branches `resultados-ataque` e `resultados-onda`).

Uma quebra é qualquer lugar em que os zeros saem do comportamento típico. Com os índices certificados pela Arb
(`N(t)` exato) e os pontos de Gram `g_m` (`θ(g_m) = mπ`, onde `ζ(½ + ig_m)` é real), `S(g_m) = N(g_m) − m − 1` é
inteiro e o ponto é "bom" quando ele é par. As seis quebras procuradas:

1. contagem: zeros fora da reta (`N(t)` maior que os zeros na reta) — a quebra que um zero fora da reta causaria;
2. lei de Gram: intervalos `[g_m, g_{m+1})` com 0, 2 ou 3 zeros;
3. regra de Rosser: um bloco de Gram de `k` intervalos sem exatamente `k` zeros (a quebra clássica mais rara);
4. `S(t)` extremo contra Selberg (média 0, variância `log log T / (2π²)`);
5. espaçamentos extremos contra o GUE (`s_min ≈ (9/(π²N))^{1/3}`, `s_max ≈ √((π/4) ln N)`);
6. par de Lehmer com `λ ≥ 0` (já colidido em `t = 0`).

**Na faixa certificada** (seção 13: 41 393 zeros, `T_PT < t ≤ g_b + 5000`):

| quebra | resultado |
|---|---|
| contagem | 0 zeros fora da reta |
| lei de Gram | 20,6% dos pontos de Gram ruins; 29,6% dos intervalos fora da lei (6 172 com 0 zeros, 6 017 com 2, **77 com 3**) |
| regra de Rosser | **1 violação** (2 blocos): o ponto de Gram `m = 12 363 153 449 050` abre um bloco de comprimento 1 com **3 zeros**, seguido de um bloco de comprimento 2 com **0 zeros** |
| `S(t)` | máximo **2,041** (4,9 σ) no zero 12 363 153 449 054 — no mesmo lugar da violação de Rosser; mínimo −1,981 (−4,8 σ) no zero 12 363 153 471 562 |
| espaçamentos | `s_min = 0,0342` (GUE: 0,028), `s_max = 2,950` (GUE: 2,890) |
| `λ ≥ 0` | nenhum; o mais perto de 0 é `−3,19·10⁻⁵` (par 12 363 153 465 694) |

A quebra mais forte da faixa é o aglomerado em `t ≈ 3 000 175 335 583,73 … 583,87`: três zeros (12 363 153 449 052,
…053, …054, com o par 052/053 a 0,0316 de distância) espremidos num só intervalo de Gram, `S(t)` subindo a 2,04, e
depois um vazio de 2,2 intervalos até o próximo zero. É onde a regra de Rosser falha e onde a contagem por trocas de
sinal nos pontos de Gram erraria; a contagem de Turing da Arb fecha ali também: os três zeros estão na reta.

As varreduras novas (`varre2.py`, usado pela onda do ataque) fazem a mesma detecção em cada bloco de 10 000 zeros, e
o ataque roda `quebras.py` em todas as listas completas (faixa da seção 13 e janelas das alturas).

**O que NÃO é**: violações de Rosser e `S(t)` grande são irregularidades conhecidas e esperadas (a primeira violação
de Rosser está perto do zero 13 999 525); nenhuma é zero fora da reta, e todas aparecem com a contagem fechando.
`OPEN_MATH = true`.

## 25. Todos os nós onde um zero fora da reta poderia estar, e o ataque em cada um

Arquivos: `computations/nos/nos.py`, `computations/nos/ataca_nos.py`, `computations/nos/resumo_nos.py`,
`.github/workflows/nos.yml` (resultado na branch `resultados-nos`), `computations/nos/resultados/`.

**Os nós.** Em cada lista certificada, `nos.py` marca os trechos curtos em que os zeros fogem do típico: aglomerações
e vazios (excesso ou falta de zeros em janelas de 2, 5, 10 e 25 espaçamentos médios, contra a variância de número do
GUE), intervalos de Gram com 3 zeros, violações de Rosser, `|S(t)|` além de 4 desvios de Selberg e pares com `s < 0,08`;
nós que se tocam viram um só, ordenados por quantos tipos de anomalia juntam.

Na faixa da seção 13: 17 aglomerações, 19 vazios, 77 intervalos de Gram com 3
zeros, 1 violação de Rosser, 95 pontos com `S` extremo, 14 pares frágeis. Os dez
nós mais fortes:

| índices | `t` (início) | tipos | o que é |
|---|---|---|---|
| 12363153449051–12363153449061 | 3000175335583.5382404124 | Gram triplo/Rosser/S extremo/vazio | Rosser: bloco de 1 intervalos com 3 zeros (g_12363153449050) |
| 12363153461936–12363153461951 | 3000175338593.8758254031 | S extremo/aglomeração/vazio | vazio L=5: 3 zeros onde se esperam 5 (Σ = 0.620) |
| 12363153475647–12363153475653 | 3000175341797.5889242977 | S extremo/aglomeração | S extremo: S = -0.692 logo depois do zero (−1.692 antes) |
| 12363153470346–12363153470354 | 3000175340559.2460942361 | S extremo/aglomeração | aglomeração L=5: 8 zeros onde se esperam 5 (Σ = 0.620) |
| 12363153453044–12363153453068 | 3000175336516.3577681856 | S extremo/vazio | S extremo: S = 1.935 logo depois do zero (−-0.935 antes) |
| 12363153440983–12363153440993 | 3000175333698.3233541651 | S extremo/vazio | vazio L=10: 8 zeros onde se esperam 10 (Σ = 0.674) |
| 12363153457676–12363153457681 | 3000175337598.5655661999 | S extremo/vazio | vazio L=5: 3 zeros onde se esperam 5 (Σ = 0.620) |
| 12363153441244–12363153441250 | 3000175333759.5644196185 | Gram triplo/S extremo | Gram triplo: 3 zeros em [g_12363153441243, g_12363153441244) |
| 12363153459933–12363153459947 | 3000175338126.2581073803 | S extremo/aglomeração | S extremo: S = -0.729 logo depois do zero (−1.729 antes) |
| 12363153451456–12363153451465 | 3000175336145.3595681893 | S extremo/vazio | S extremo: S = 1.783 logo depois do zero (−-0.783 antes) |

**O ataque** (`ataca_nos.py`, no workflow): para cada nó, os zeros de novo pelo método local de Platt com 384 bits
(têm de cair nas bolas da lista), nos mais fortes também pelo método geral da Arb (Gram/Rosser/Turing), e `N(T)` exato
nos pontos médios antes e depois do nó. `N(T_a) = a − 1` e `N(T_b) = b` quer dizer que os zeros do nó, todos na reta,
são os únicos zeros de `ζ` em `0 < Re s < 1` naquela faixa de alturas: nenhum quarteto no nó. O workflow roda em todas
as listas certificadas (faixa da seção 13, janelas das alturas, continuação contígua) assim que elas ficam prontas.

**Resultado** (run 41560374464, branch `resultados-nos`): 25 nós atacados na faixa da seção 13, **contagem local
fechando nos 25**. Em todos, os zeros recalculados pelo método local de Platt com 384 bits caem nas bolas da lista
(raios até 5·10⁻³⁶); nos 6 mais fortes o método geral da Arb (Gram/Rosser/Turing) dá os mesmos zeros. No
aglomerado: `N(T_a) = 12 363 153 449 050` e `N(T_b) = 12 363 153 449 061` com `T_a = …583,3969` e `T_b = …586,1004`,
os 11 zeros do nó na reta. Pela paridade no kernel (seção 26, `Paridade.fecha_de_contagens`,
`Paridade.no_aglomerado_sem_fora`), essas duas contagens implicam que não há zero fora da reta nessa janela; um furo
teria aparecido como diferença de pelo menos 2 (`Paridade.furo_de_dois`).

**O que NÃO é**: aglomerações, vazios e violações de Rosser são irregularidades esperadas numa sequência do tipo GUE;
um nó só seria zero fora da reta se a contagem local não fechasse. `OPEN_MATH = true`.

## 26. Formalização dos cálculos: o que o kernel confere em cada número

Arquivos: `ClayRiemannProof/Lehmer.lean`, `ClayRiemannProof/Paridade.lean`, `ClayRiemannProof/Gram.lean`,
`ClayRiemannProof/QuartetoDesenhado.lean`.

Os números das seções 13, 16, 24 e 25 vêm da Arb, fora do kernel. Cada lei que leva desses números a uma conclusão
agora está no kernel. Os números entram como hipóteses nomeadas (bolas `|γ − c| ≤ r`, valores de `N` nos pontos de
Gram, a condição de Lehmer `Δ²g ≤ 4/5`) e o kernel confere a aritmética.

| cálculo | lei | no kernel |
|---|---|---|
| contagem de Turing numa janela | zeros fora da reta vêm aos pares `ρ`, `1 − ρ̄` na mesma altura: são em número par | `Paridade.fora_par` |
| contagem que fecha | zeros na janela = zeros na reta ⟹ nenhum fora da reta | `Paridade.contagem_fecha`, `Paridade.fecha_de_contagens` |
| o nó do aglomerado (seção 25) | `N(T_b) − N(T_a) = 11` e 11 zeros na reta ⟹ nenhum fora | `Paridade.no_aglomerado_sem_fora` |
| contagem que não fecha | a diferença é **pelo menos 2**, nunca 1 | `Paridade.furo_de_dois` |
| lei de Gram | `S(g_m) = N(g_m) − m − 1` é inteiro; zeros no bloco = comprimento + variação de `S` | `Gram.S_gram`, `Gram.zeros_no_bloco` |
| regra de Rosser | entre dois pontos de Gram bons, excesso e falta só de 2 em 2 | `Gram.bloco_par` |
| o aglomerado | pontos bons, `S = 0, 2, 0`, bloco de comprimento 1 com 3 zeros e bloco de comprimento 2 com 0 | `Gram.aglomerado_rosser` |
| cota de CSV de um par de Lehmer | `−(5/32)Δ² ≤ λ ≤ −Δ²/8` para `Δ²g ≤ 4/5`; logo `λ < 0` | `Lehmer.csv_ge`, `Lehmer.csv_le_isolado`, `Lehmer.csv_neg` |
| CSV e a lei da colisão (seção 16) | sem vizinhos (`g → 0⁺`), `λ → −Δ²/8` | `Lehmer.csv_limite` |
| unidades | em `x = c·γ`, `λ` vezes `c²`; de `γ` para `x = 2γ` (o tempo de de Bruijn), vezes 4 | `Lehmer.csv_escala`, `Lehmer.csv_x_de_gamma` |
| par 052/053 do aglomerado | `−6,23·10⁻⁴ ≤ λ ≤ −4,98·10⁻⁴` para todo `g` | `Lehmer.aglomerado_052_053` |
| par mais frágil (694/695) | `−3,99·10⁻⁵ ≤ λ ≤ −3,18·10⁻⁵` para todo `g` | `Lehmer.par_mais_fragil` |
| par mais frágil da fronteira em 10¹⁸ | `λ ∈ [−1,013·10⁻⁵, −8,09·10⁻⁶]` | `Continuacao.par_mais_fragil_1e18` |
| continuação contígua até `…822 471,5` | RH até 3 000 175 822 471 (condicional às janelas); par mais frágil `λ ∈ [−5,75·10⁻⁷, −4,59·10⁻⁷]` | `Continuacao.rhAteZ_continuacao`, `Continuacao.par_mais_fragil_continuacao` |
| quarteto desenhado em `0,3 ± 14i`, `0,7 ± 14i` | `|ζ| ≥ 1/10` nos quatro pontos (avaliação certificada no kernel) | `QuartetoDesenhado.quarteto_desenhado` |

**O aglomerado, conferido na lista certificada** (`t − 3 000 175 335 000`):

| | `t` | distância ao próximo | `s` | `S` logo depois |
|---|---|---|---|---|
| zero …051 | 583,53824041 | 0,1945668 | 0,8327 | 0,454 |
| zero …052 | 583,73280730 | 0,0315609 | 0,1351 | 0,621 |
| zero …053 | 583,76436820 | 0,1039775 | 0,4450 | 1,486 |
| zero …054 | 583,86834571 | 0,5180912 | 2,2174 | **2,041** |
| zero …055 | 584,38643694 | 0,2753771 | 1,1786 | 0,823 |

Pontos de Gram: `g_{…050} = 583,64425247`, `g_{…051} = 583,87789923`, `g_{…052} = 584,11154599`,
`g_{…053} = 584,34519274` (espaçamento 0,233647). O intervalo `[g_{…050}, g_{…051})` tem os zeros 052, 053 e 054;
`[g_{…051}, g_{…053})` não tem nenhum. A exceção de Rosser (no sentido estrito, bloco com menos zeros que intervalos)
é o bloco vazio `[g_{…051}, g_{…053}]`; os dois zeros que faltam nele estão no intervalo anterior. Para o par 052/053,
`g` (±300 vizinhos e a cauda pela densidade, em `x = 2γ`) é 57,673, `Δ²g = 0,2298` e `λ = −5,143·10⁻⁴`, dentro do
intervalo do kernel. Em coordenadas `γ` o mesmo número é `−1,286·10⁻⁴` (um quarto). O tempo do fluxo de de Bruijn
é o de `x`.

Na faixa há 202 nós distintos. A soma 17 + 19 + 77 + 1 + 95 + 14 = 223 conta duas vezes um nó com dois tipos.

**A continuação contígua** (run 41559243734, branch `resultados-continuacao`; `ClayRiemannProof/Continuacao.lean`):
quatro faixas de 120 000 unidades acima da seção 13, `3 000 175 342 471,5 < Im s ≤ 3 000 175 822 471,5`, com
2 054 383 zeros, todos na reta. Em cada faixa `N(b) − N(a)` = zeros na reta (déficit 0), as faixas colam (o `N`
na mesma altura é igual pelas duas) e o maior raio é 5,01·10⁻¹⁸. No kernel: com Platt–Trudgian e as duas janelas
como hipóteses nomeadas, RH até 3 000 175 822 471 (`Continuacao.rhAteZ_continuacao`), e o primeiro zero fora da
reta, se existir, está acima disso (`Continuacao.primeiro_fora_acima_continuacao`). O par mais próximo dos 2 milhões
de zeros (12 363 153 756 750/…751, `t ≈ 3 000 175 407 476,415`, a 0,000958 um do outro, `s = 0,0041`) tem
`−5,75·10⁻⁷ ≤ λ ≤ −4,59·10⁻⁷` (`Continuacao.par_mais_fragil_continuacao`; CSV calculado: −4,593·10⁻⁷). É o par
mais perto da colisão em todos os dados, cerca de 70 vezes mais perto de `0⁻` que o da seção 13, e ainda negativo,
como a cota exige. A agregação do workflow parou num erro de serialização (booleano do numpy no JSON) depois de
gravar as quatro faixas; a colagem e os pares foram refeitos com o mesmo `agrega.py` fora do CI.

**O que NÃO é**: os teoremas com hipóteses de dados não provam os dados. Eles dizem: se as bolas da Arb estão certas,
então isto vale. O teorema de Csordas–Smith–Varga (`Λ ≥ λ`) não está no kernel. Nada aqui prova ou refuta RH.
`OPEN_MATH = true`.

## 27. A força mínima que tira um par de zeros da reta: os pontos mais fáceis

Arquivos: `ClayRiemannProof/Forca.lean`, `computations/forca/forca_rs.py` (estimativa por Riemann–Siegel),
`computations/forca/forca.c` e `forca_arb.py` (bolas da Arb; workflow `forca.yml`, branch `resultados-forca`),
`computations/forca/resultados/`.

**A força.** Na reta, `ζ(½ + it) = e^{−iθ(t)} Z(t)` com `Z` real. Entre dois zeros vizinhos, `Z` faz uma lombada de
altura `|Z*|`. Um empurrão `ε` que preserve as simetrias de `ζ` (equação funcional e conjugação: `Z` continua real)
só tira os dois zeros da reta quando passa da altura da lombada. No kernel (`Forca.lombada_reais_iff`,
`Forca.par_fora_da_reta`, `Forca.limiar_do_par`):

    ε ≤ |Z*|  ⟺  os dois zeros ficam na reta;     ε > |Z*|  ⟹  ½ ± b + it*,   b = √(2(ε − |Z*|)/|Z''|),

e com a conjugação, o quarteto `½ ± b ± it*`. No modelo do par, `|Z*| = |Z''|Δ²/8`. A outra força é o tempo do fluxo
de de Bruijn: voltar o tempo de `|t|` é empurrar `2|t|` (`Forca.calor_eh_empurrao`), e o par isolado colide em
`Δ_x²/8` (`x = 2γ`, seção 16). O par mais apertado tem o menor tempo do calor, mas o menor empurrão é o de
`|Z''|Δ²` menor: não é o mesmo ponto.

**Os pontos mais fáceis em 3·10¹²** (Riemann–Siegel com 691 010 termos e fases com 60 dígitos, nos 300 pares mais
apertados dos 2 095 776 zeros da seção 13 e da continuação; conferência: `|Z|` nos próprios zeros ≤ 1·10⁻⁸, quatro
ordens abaixo das forças; a força relativa divide pela média quadrática de `Z`, `√log(t/2π) ≈ 5,19`):

| par (índice) | `t` (início) | `Δ` | `s` | força `|Z*|` | relativa | `Z''` | tempo do calor `Δ_x²/8` |
|---|---|---|---|---|---|---|---|
| **12 363 153 570 515** | 3 000 175 363 963,243 | 0,002058 | 0,0088 | **5,3·10⁻⁵** | 1,0·10⁻⁵ | −101 | 2,1·10⁻⁶ |
| 12 363 153 765 891 | 3 000 175 409 612,264 | 0,002854 | 0,0122 | 1,05·10⁻⁴ | 2,0·10⁻⁵ | −103 | 4,1·10⁻⁶ |
| 12 363 153 756 750 | 3 000 175 407 476,415 | 0,000958 | 0,0041 | 1,23·10⁻⁴ | 2,4·10⁻⁵ | +1 069 | **4,6·10⁻⁷** |
| 12 363 153 873 626 | 3 000 175 434 784,313 | 0,002166 | 0,0093 | 1,23·10⁻⁴ | 2,4·10⁻⁵ | +210 | 2,3·10⁻⁶ |
| 12 363 153 976 477 | 3 000 175 458 815,179 | 0,006793 | 0,0291 | 1,30·10⁻⁴ | 2,5·10⁻⁵ | −23 | 2,3·10⁻⁵ |
| 12 363 155 255 037 | 3 000 175 757 546,373 | 0,002182 | 0,0093 | 1,35·10⁻⁴ | 2,6·10⁻⁵ | −227 | 2,4·10⁻⁶ |

O ponto mais fácil por empurrão é o par 12 363 153 570 515: um empurrão de 5,3·10⁻⁵ (cerca de 10⁻⁵ do tamanho típico
de `Z`) num trecho de 0,002 junta os dois zeros. Logo acima disso o par sai da reta: com `ε = |Z*| + b²|Z''|/2`, `b =
0,001` pede `ε ≈ 1,04·10⁻⁴` e `b = 0,01` pede `ε ≈ 5,1·10⁻³`. Um quarteto visível como `0,3/0,7 ± 14i` (`b = 0,2`, da
ordem do espaçamento) já sai do modelo quadrático: precisaria mudar `Z` na escala do próprio `Z`, e na altura 14 o
kernel refuta esse quarteto (seção 26). O par 976 477 é largo (`s = 0,029`) e mesmo assim está entre os seis mais
fáceis, porque ali `Z` é quase plano (`|Z''| ≈ 23`).

**Os nós da seção 25, pela força** (o menor `|Z*|` dentro de cada nó; os 25 atacados):

| nó | tipos | força mínima | par |
|---|---|---|---|
| 12363153465693–697 | S extremo / par frágil | **1,03·10⁻³** | 465 694 (`s = 0,0342`) |
| 12363153463169–172 | Gram triplo / par frágil | 1,85·10⁻³ | 463 170 |
| 12363153459933–947 | S extremo / aglomeração | 3,11·10⁻³ | 459 936 |
| 12363153473934–938 | S extremo / par frágil | 6,06·10⁻³ | 473 936 |
| 12363153449051–061 | Gram triplo / Rosser / S extremo / vazio (o aglomerado) | 7,72·10⁻³ | 449 052 |
| os 20 restantes | S extremo, vazio, aglomeração | 1,2·10⁻² a 0,45 | |

O nó do aglomerado de Rosser, a quebra mais forte da contagem, precisa de 7,5 vezes mais força que o par frágil
465 694 e de 145 vezes mais que o ponto mais fácil da continuação. `S(t)` extremo mede excesso ou falta de zeros na
contagem, não proximidade de dois zeros; os nós que só têm `S` extremo estão entre os mais duros (0,07 a 0,45).

**As alturas** (seção 18; run 41588835957): 10¹⁴ e 10¹⁶ certificadas, 20 000 zeros cada, contagem fechando e índice
conferindo. Em 10¹⁴: `s_min = 0,0323`, `λ = −2,23·10⁻⁵` (previsto `−2,73·10⁻⁵`). Em 10¹⁶ apareceu um par com
`s = 0,0078` em só 20 000 zeros (o GUE espera 0,036; acontece com probabilidade de cerca de 1%), `λ = −9,73·10⁻⁷`:
o par mais perto da colisão por zero varrido em todos os dados.

**A força certificada pela Arb não saiu** (run 41603222260, branch `resultados-forca`). Nos quatro grupos
(3·10¹², 10¹⁴, 10¹⁶, 10¹⁸), a primeira avaliação de `Z` com três derivadas (`acb_dirichlet_hardy_z`, 256 bits) no
extremo da lombada passou do limite de 19 000 s por chamada sem terminar. Isso aconteceu inclusive em `3·10¹²`, onde a
soma de Riemann–Siegel em ponto flutuante leva menos de um segundo. Os outros pares de cada grupo ficaram sem
orçamento. As forças desta seção continuam sendo estimativas de Riemann–Siegel conferidas nos zeros (`|Z|` nos
próprios zeros ≤ 10⁻⁸, quatro ordens abaixo das forças). Certificá-las pede outro caminho: por exemplo, cotas de `Z`
entre os dois zeros a partir das bolas do método de Platt, que já são certificadas.

**O que NÃO é**: `ζ` não muda; as forças medem quão perto `ζ` está, em cada ponto, de uma função com as mesmas
simetrias e um zero fora da reta ali. Toda força medida é positiva, e é isso que significa todos os zeros estarem na
reta. Mudar `ζ` de verdade quebra o produto de Euler (é o que faz Davenport–Heilbronn, seção 18). As forças de
Riemann–Siegel são estimativas em ponto flutuante conferidas nos zeros; a tentativa de certificá-las pela Arb não
terminou (acima). Nada aqui
prova ou refuta RH. `OPEN_MATH = true`.

## 28. Mudando `Z` na escala do próprio `Z`

Arquivos: `computations/forca/lombadas.py`, `escala.py`, `trilha.py`, `computations/forca/resultados/`
(`lombadas_faixa_3e12.json.gz`, `escala_faixa_3e12.json`).

**A função empurrada.** `Z − ε` na reta é `ζ_ε(s) = ζ(s) − ε·χ(s)^{1/2}` no plano (`χ(s) = ζ(s)/ζ(1 − s)`, e
`χ(½ + it)^{1/2} = e^{−iθ(t)}`). `ζ_ε` tem a mesma equação funcional (`ζ_ε(s) = χ(s)ζ_ε(1 − s)`) e a mesma conjugação
de `ζ`, e não tem produto de Euler. Por isso seus zeros fora da reta vêm em quartetos `½ ± b ± it`. No kernel, na
forma de `ξ`: `Forca.empurrao_simetrico` (com `f` e `g` simétricas e `ε` real, `f − ε·g` é simétrica),
`Forca.constante_simetrica` (`g = 1` serve) e `Forca.zeta_empurrada_quarteto` (os zeros de `ξ(½ + w) − ε·g(w)` vêm em
quartetos `w, −w, w̄, −w̄`), só com `propext`, `Classical.choice` e `Quot.sound`. `Z − ε` (ε > 0) só
perde zeros reais nas lombadas positivas: cada lombada positiva mais baixa que `ε` é engolida e seus dois zeros saem
da reta. `Z + ε` faz o mesmo com as negativas.

**Todas as lombadas da faixa da seção 13** (41 393 zeros, 41 392 lombadas; `Z`, `Z'`, `Z''` por Riemann–Siegel no
ponto médio e um passo de Newton até o extremo; média quadrática de `Z`: `√log(t/2π) = 5,19`):

| `ε` | `ε`/média quadrática | zeros fora da reta, `Z − ε` | `Z + ε` |
|---|---|---|---|
| 1·10⁻³ | 2·10⁻⁴ | 0 | 0 |
| 3,2·10⁻³ | 6·10⁻⁴ | 2 (0,005%) | 12 (0,03%) |
| 1·10⁻² | 2·10⁻³ | 64 (0,16%) | 64 (0,16%) |
| 0,1 | 0,02 | 1 404 (3,4%) | 1 382 (3,3%) |
| 0,32 | 0,06 | 5 668 (13,7%) | 5 472 (13,2%) |
| 1 | 0,19 | 16 314 (39%) | 16 020 (39%) |
| 1,78 | 0,34 | 23 474 (57%) | 23 224 (56%) |
| 3,16 | 0,61 | 30 208 (73%) | 30 234 (73%) |
| 5,6 | 1,1 | 35 598 (86%) | 35 536 (86%) |
| 10 | 1,9 | 38 924 (94%) | 38 940 (94%) |
| 31,6 | 6,1 | 41 152 (99,4%) | 41 180 (99,5%) |
| 129,5 | 25 | todos | todos (a partir de 110,2) |

As alturas das lombadas: mediana 1,43 (0,28 da média quadrática); 1% abaixo de 0,041; a mais baixa é a do par frágil
465 694 (−1,03·10⁻³), a mais baixa positiva a do par 470 301 (2,97·10⁻³). A mais alta (129,5) fica no maior vazio
da faixa (zeros 448 671/672, intervalo 0,657, `s = 2,81`, `t ≈ 3 000 175 335 494,90`): é o ponto mais rígido, onde
só um empurrão de 25 vezes a média quadrática tira os zeros da reta.

**O caminho dos zeros até o quarteto visível** (o zero de `Z(t* + u) − sinal(Z*)·ε` com `u` complexo, seguido em `ε`;
`b = |Im u|` é a distância à reta; os 15 pontos: os seis mais fáceis da continuação e os nós mais fortes da faixa;
`computations/forca/resultados/trilha_3e12.json`):

| par | `|Z*|` | `Z''` | `b = 0,001` | `b = 0,01` | `b = 0,05` | `b = 0,1` | `b = 0,2` |
|---|---|---|---|---|---|---|---|
| 12 363 153 976 477 | 1,30·10⁻⁴ | −22,6 | 1,4·10⁻⁴ | 1,3·10⁻³ | 0,039 | 0,26 | **2,56** |
| nó 459 933–947 | 3,11·10⁻³ | +45,6 | 3,1·10⁻³ | 5,5·10⁻³ | 0,065 | 0,32 | 2,65 |
| nó 461 936–951 | 0,0571 | −51,5 | 0,057 | 0,060 | 0,129 | 0,41 | 2,93 |
| 12 363 153 765 891 | 1,05·10⁻⁴ | −103 | 1,6·10⁻⁴ | 5,3·10⁻³ | 0,136 | 0,63 | 4,33 |
| 12 363 153 570 515 (o mais fácil no limiar) | 5,3·10⁻⁵ | −101 | 1,04·10⁻⁴ | 5,1·10⁻³ | 0,134 | 0,64 | 4,63 |
| nó 463 169–172 (Gram triplo) | 1,85·10⁻³ | +72,3 | 1,9·10⁻³ | 5,5·10⁻³ | 0,106 | 0,57 | 4,82 |
| aglomerado de Rosser 052/053 | 7,72·10⁻³ | +62,9 | 7,8·10⁻³ | 0,011 | 0,098 | 0,51 | 4,92 |
| nó 465 693–697 (par frágil 465 694) | 1,03·10⁻³ | +130 | 1,1·10⁻³ | 7,6·10⁻³ | 0,177 | 0,87 | 6,60 |
| nó 440 983–993 | 0,0124 | −74,6 | 0,0125 | 0,016 | 0,131 | 0,75 | 7,12 |
| nó 473 934–938 | 6,06·10⁻³ | +183 | 6,2·10⁻³ | 0,016 | 0,254 | 1,22 | 8,79 |
| 12 363 155 255 037 | 1,35·10⁻⁴ | −227 | 2,5·10⁻⁴ | 0,012 | 0,297 | 1,36 | 8,82 |
| 12 363 153 873 626 | 1,23·10⁻⁴ | +210 | 2,3·10⁻⁴ | 0,011 | 0,281 | 1,34 | 9,23 |
| aglomerado de Rosser 053/054 | 0,0984 | −113 | 0,098 | 0,105 | 0,286 | 1,37 | 13,2 |
| nó 455 300–304 (o mais duro) | 0,455 | +453 | 0,455 | 0,48 | 1,09 | 3,41 | 21,3 |
| 12 363 153 756 750 (o mais apertado) | 1,23·10⁻⁴ | +1 069 | 6,6·10⁻⁴ | 0,054 | 1,4 | 6,3 | não chega (`b` máx. 0,194 com `ε = 34`) |

Até `b ≈ 0,05` vale o modelo quadrático (`ε = |Z*| + b²|Z''|/2`). Depois disso o par se afasta mais devagar que o
modelo prevê: em `b = 0,2` o `ε` medido é 1,9 a 5,7 vezes o do modelo (4,63 contra 2,0 no par 570 515). O caminho
inteiro é monótono nos 15 pontos e os valores de `ε` coincidem, até o terceiro algarismo, em duas execuções com bases
de fase diferentes. (O campo `convergiu` fica falso em parte dos passos porque o critério `|passo| < 10⁻¹³` está
abaixo do ruído de ponto flutuante de `Z` em `3·10¹²`, ≈ 10⁻¹⁰.)

**Quem chega primeiro ao quarteto visível não é quem sai primeiro da reta.** Perto do limiar manda a altura da
lombada `|Z*|`: o par 570 515 sai com `ε = 5,3·10⁻⁵`. Em `b = 0,2` manda a curvatura: a ordem dos 14 pontos que chegam
lá segue `|Z''|` (correlação de postos de Spearman 0,86; com `|Z*|`, 0,38). O mais fácil é o par 976 477, largo e com a
lombada mais chata (`Z'' = −22,6`, `ε = 2,56`, metade da média quadrática de `Z`). Logo depois vêm dois nós da faixa
com `|Z*|` 24 e 440 vezes maior, mas curvatura pequena. Os que resistem são os de `Z` íngreme: o nó 455 300–304 pede
`ε = 21,3` (4 vezes a média quadrática), e o par mais apertado (`Z'' = +1 069`) não passa de `b = 0,194` com `ε = 34`.
Um quarteto visível pede sempre mudar `Z` na escala do próprio `Z`.

**A leitura.** Com `ε` da ordem de `Z`, 86% dos zeros saem da reta, sempre em quartetos. A reta só segura todos os
zeros para `ε` menor que a lombada mais baixa, e a lombada mais baixa desce quando se olham mais zeros: 1,03·10⁻³ em
41 393 zeros e 5,3·10⁻⁵ em 2 095 776 (51 vezes mais zeros, lombada 19 vezes mais baixa). Pela repulsão do GUE,
`|Z*|_min ≈ |Z''|Δ_min²/8` desce como `N^{−2/3}`, logo qualquer empurrão fixo `ε > 0` acaba tirando zeros da reta em
algum lugar mais alto. É a versão por empurrão do que Rodgers–Tao provaram para o fluxo do calor (`Λ ≥ 0`: qualquer
tempo `t < 0` cria zeros fora da reta). Aqui é observação nos dados, não teorema. A reta é propriedade de `ζ`
exatamente, não de uma vizinhança de `ζ`. `OPEN_MATH = true`.

**A largura das lombadas cresce como `½ log log T`** (`computations/forca/loglog.py`, `resultados/loglog.json`).
A variância de `log|Z*|` é 1,804 ± 0,014 nas 41 392 lombadas de `3·10¹²` e 1,896 ± 0,063 numa amostra de 2 000
lombadas da janela certificada de `10¹⁴` (`resultados/lombadas_1e14_amostra.json.gz`). Selberg e o CUE preveem um
aumento de 0,061; o medido é 0,09 ± 0,06. Com só essas duas alturas (`Δ log L = 0,12`) a inclinação fica mal
determinada (`0,75 ± 0,52`). Nos sete tamanhos do CUE da seção 35 (`N = 27` a `2 301`), o ajuste
`var = A·log N + B` dá `A = 0,516` e `B = 0,21`, com resíduo máximo de 0,10; Selberg prevê `A = ½`. A mediana fica em
1,40 ± 0,04 em todos os tamanhos. Um modelo lognormal com essa mediana e essa variância bate com o próprio CUE em
`N = 2 301` a menos de um ponto (43,5% contra 44,1% com `ε = 1`; 95,8% contra 96,2% com `ε` = média quadrática). Na
amostra de `10¹⁴` o CUE também acerta: 40,2% medido contra 39,5% com `ε = 1`, e 85,3% contra 84,9% com
`ε = √log(T/2π)`.

Extrapolando (é extrapolação condicional: o CUE é modelo, e a lei de Selberg é teorema para `t` aleatório, não para
lombadas):

| altura | var. de `log` lombada | tirados com `ε = 1` | com `ε` = 0,1 da média quadrática | com `ε` = média quadrática |
|---|---|---|---|---|
| 3·10¹² (medido) | 1,80 | 39% | 22% | 84% |
| 10¹⁰⁰⁰ | 4,2 | 44% | 73% | 96% |
| 10^(10⁹) | 11,3 | 46% | 99,2% | 99,90% |
| 10^(10²⁴) | 29,1 | 48% | 99,9999% | 1 − 1,4·10⁻⁷ |
| 10^(10^(11·10^7000000)) | 13,1·10^7000000 | → ½ | → 1 | 1 − 10^(−2,67·10^7000000) |

Com a mediana parada perto de 1,4 e a largura crescendo sem limite, um empurrão fixo tira da reta uma fração que
tende a ½. Um empurrão proporcional à média quadrática tira todos os pares, menos uma fração que vai a zero. Isso
corrige os números da conta rápida feita antes (lognormal com `A = ½` exato e sem calibração).

## 29. Leis, operadores e teoremas: o documento em domínio público

Arquivo: [`LEIS.md`](LEIS.md) (CC0 1.0, ORCID 0009-0006-6874-3910). Junta tudo o que saiu das seções 13 a 28: os
teoremas no kernel com o nome exato, os teoremas com hipótese nomeada (dados da Arb), os teoremas clássicos ligados
aos dados com o teste que os dados permitem, as leis empíricas, os operadores e conjuntos e as linhas de pesquisa
abertas, cada uma classificada (ferramenta, consequência, reformulação ou candidata a novo, que só vira novo com uma
Proposta R1xx aceita).

Dois testes novos de teoremas clássicos nas 41 392 lombadas da seção 13:

- **Conrey–Ghosh e Hughes–Lugmayer–Pearce-Crump (2024)**, sob RH: média de `Z*²` medida 34,91 ± 1,13; previsto 34,90
  com os termos de ordem menor (`aL + 2a + α₋₁`, `a = (e² − 5)/2`, `α₋₁ = 5 − e² − 10γ₀ + 2e²γ₀`), 32,12 só com o
  termo principal.
- **A lombada do par**: `log|Z*| = 2,02·log Δ + c` nos 1 119 pares com `s < 0,3`, a lei `|Z*| = |Z''|Δ²/8`
  (`Forca.limiar_do_par`) nos dados.

E o operador de empurrão (`ClayRiemannProof/Empurrao.lean`, no kernel): contagem monótona, limiar da janela, soma em
janelas disjuntas, semigrupo de translações, mínimo que só desce com a janela, e o teorema condicional "se a lombada
mais baixa tende a 0, todo empurrão fixo acaba tirando zeros da reta". Gráfico da fração tirada da reta:
`computations/forca/resultados/fracao_fora.png`.

**Licença do repositório**: CC0 1.0 (domínio público), arquivo `LICENSE`.

## 30. As leis por trás dos gráficos: `S(t)`, Gram e Rosser; unidades de de Bruijn; matrizes; habitantes (teorema)

Arquivo: `ClayRiemannProof/Leis.lean`.

```lean
-- S(t) = N(t) − θ(t)/π − 1, N(t) = N₀ + #{γ ≤ t}
theorem lei_mestra (h : t₁ ≤ t₂) : S t₂ − S t₁ = #zeros(t₁, t₂] − (θ t₂ − θ t₁)/π
theorem lei_vazio (hθ : StrictMono θ) (h : t₁ < t₂) (hv : entre t₁ t₂ = 0) : … ∧ S t₂ < S t₁   -- o vazio faz S descer
theorem S_gram (hg : θ g = m·π) : S g = N(g) − m − 1                                         -- inteiro em Gram
theorem lei_gram : S g_{m+k} − S g_m = #zeros(g_m, g_{m+k}] − k
theorem vazio_gram (hv : sem zeros) : S g_{m+k} = S g_m − k
theorem gram_triplo (3 zeros em um intervalo) : S g_{m+1} = S g_m + 2
theorem rosser_bloco : S g_{m+k} = S g_m ↔ #zeros = k
theorem aglomerado_e_vazio (3 zeros, depois 2 intervalos vazios) : S g_{m+3} = S g_m
-- de Bruijn: s = ½ + iz/2
theorem re_s_de_z (z) : (½ + I z/2).re − ½ = −(Im z)/2
theorem colisao_em_gama : zeros reais ↔ −Δγ²/2 ≤ t                                   -- Δz = 2Δγ
theorem colisao_par_mais_fragil : −(0,007987)²/2 = −63 792 169/(2·10¹²) ∈ (−3,2·10⁻⁵, −3,1·10⁻⁵)
theorem sem_deslocamento_em_2e5 : em t = −2·10⁻⁵ o par mais frágil ainda está na reta
theorem deslocamento_forcado (ht : t ≤ −Δγ²/2) : ∃ z, … Re s − ½ = −√(−Δγ² − 2t)/2
-- matrizes no vetor (Re s − ½, Im s)
theorem vec_tensao : vec (tensao s) = diag(−1, −1) *ᵥ vec s      -- vec_espelho, vec_torcao
theorem klein : involuções; espelho·tensão = torção; …
-- produto e habitantes
theorem produto_quarteto : (w − z)(w + z)(w − z̄)(w + z̄) = w⁴ − 2 Re(z²) w² + |z|⁴
theorem produto_na_reta (Re z = 0) : … = (w² + (Im z)²)²
theorem target_iff_fora_vazio : Target ↔ Fora = ∅
theorem fora_vazio_ou_quatro : Fora = ∅ ∨ 4 ≤ Fora.encard
theorem classes_orbita : (orbita s).card = 2 ∨ (orbita s).card = 4
theorem fora_em_pares (h : ρ ∈ Fora ∩ Janela T₁ T₂) : 1 − ρ̄ ∈ Fora ∩ Janela T₁ T₂ ∧ 1 − ρ̄ ≠ ρ ∧ Im(1 − ρ̄) = Im ρ
theorem deficit_ao_menos_dois (h : (Fora ∩ Janela T₁ T₂).Nonempty) : 2 ≤ (Fora ∩ Janela T₁ T₂).encard
theorem sem_habitantes_ate_13 : {s ∈ Z | |Im s| ≤ 13} = ∅
theorem fora_ate_janela_vazio (hPT) (hJ) : {s ∈ Fora | |Im s| ≤ 3 000 175 342 471} = ∅
theorem fora_ate_continuacao_vazio (hPT) (hJ) (hC) : {s ∈ Fora | |Im s| ≤ 3 000 175 822 471} = ∅
```

**O que é**: as leis exatas por trás dos gráficos de `S(t)`, Gram, Rosser e dos pares forçados.
- **Um vazio faz `S` descer**: `S` desce `1` por intervalo de Gram sem zero, e só sobe nos zeros. Depois do aglomerado
  da violação de Rosser (`S = 2,04`), os 2,2 intervalos vazios trazem `S` de volta para perto de 0
  (`aglomerado_e_vazio`); `S` não fica parado.
- **Unidades**: na variável de de Bruijn `z = 2γ`, o par mais frágil (`Δγ = 0,007987`) colide em `−Δγ²/2 = −3,19·10⁻⁵`,
  que é o próprio `λ` da tabela. Em `t = −2·10⁻⁵` ele ainda está na reta, e depois do limiar o desvio é
  `√(−Δγ² − 2t)/2`.
- **Operadores**: as três simetrias são as matrizes de sinal do grupo de Klein.
- **Produto do quarteto**: é um polinômio par real, e na reta vira um quadrado perfeito (par duplo).
- **Habitantes**: Clay é `Fora = ∅`; `Fora` vazio ou com pelo menos 4 habitantes; órbitas só das classes 2 e 4.
- **Como um zero fora da reta apareceria numa verificação**: numa janela de alturas, `ρ` e `1 − ρ̄` estão na mesma
  altura e são distintos (`fora_em_pares`); logo o déficit `(N(T₂) − N(T₁)) − (zeros na reta)` é 0 ou pelo menos 2
  (`deficit_ao_menos_dois`; a mesma lei que `Paridade.furo_de_dois`, na forma de conjunto). Na altura do par, `N`
  sobe 2 e `S` sobe 2 (não desce), sem as duas trocas de sinal de `Z(t)` correspondentes.

Conferência independente dos números da seção 24, feita a partir da lista certificada de 41 393 zeros (fora do kernel):
- intervalos de Gram com 0, 1, 2 e 3 zeros: 6 172, 29 125, 6 017 e 77;
- 20,59% de pontos de Gram ruins;
- `S` máximo 2,0409 no zero …449 054 e `S` mínimo −1,981 antes do zero …471 562;
- uma única quebra da regra de Rosser, em `g_…449 050` (1 intervalo com 3 zeros, depois 2 com 0).

**O que NÃO é**: as leis de `S` e de Gram são identidades de contagem; não dizem onde estão os zeros. O deslocamento
forçado é do modelo `H_t` com `t < 0`, não de `ζ`. `OPEN_MATH = true`.
**Origem**: Gram (1903), Rosser–Yohe–Schoenfeld (1969), de Bruijn (1950); formalização nova. **Axiomas**: `[propext,
Classical.choice, Quot.sound]` (32 guardas).

## 31. Continuação contígua: RH conferida até 3 000 175 822 471,5 (cálculo certificado fora do kernel)

Arquivos: `computations/continuacao/` (`continua.py`, `agrega.py`, `gram.py`, `inicio.json`),
`.github/workflows/continuacao.yml`. Execução 41559243734 do GitHub Actions
(FLINT 3 / Arb, 256 bits). Faixas, zeros (`zeros{0..3}.csv.gz`) e log na raiz da branch `resultados-continuacao`;
os agregados em `computations/continuacao/resultados/de_3000175342471.5/` (`continuacao.json`, `gram.json`).

Logo acima do fim da seção 13 está onde o primeiro zero fora da reta estaria, se existisse
(`PrimeiroFora.primeiro_fora_acima_janela`). Quatro faixas contíguas de 120 000 unidades de altura:

| faixa | `(a, b]` | `N(a)` | `N(b)` | zeros na reta | déficit |
|---|---|---|---|---|---|
| 0 | `(3 000 175 342 471,5; …462 471,5]` | 12 363 153 478 531 | 12 363 153 992 127 | 513 596 | 0 |
| 1 | `(…462 471,5; …582 471,5]` | 12 363 153 992 127 | 12 363 154 505 723 | 513 596 | 0 |
| 2 | `(…582 471,5; …702 471,5]` | 12 363 154 505 723 | 12 363 155 019 318 | 513 595 | 0 |
| 3 | `(…702 471,5; …822 471,5]` | 12 363 155 019 318 | 12 363 155 532 914 | 513 596 | 0 |

- `N` exato nas cinco pontas (`acb_dirichlet_zeta_nzeros`, contagem de Turing intervalar). O `N(a)` da faixa 0 é o
  `N` do fim da seção 13, e cada `N(b)` é igual ao `N(a)` da faixa seguinte, calculado por outro job.
- 2 054 383 zeros pelo método local de Platt: índices seguidos, bolas disjuntas e em ordem, raio máximo
  `5,01·10⁻¹⁸`, todos com `Z(t) = 0`, isto é, em `Re s = ½`.
- Com Platt–Trudgian e a seção 13: todo zero não trivial com `0 < Im s ≤ 3 000 175 822 471,5` está na reta, e
  `N(3 000 175 822 471,5) = 12 363 155 532 914 = 12 363 153 437 138 + 41 393 + 2 054 383`.

**Estatística da faixa** (fora do kernel):
- espaçamento normalizado `s`: variância 0,1761 (GUE 0,1781); fração com `s < 0,08` igual a `5,30·10⁻⁴`
  (GUE `≈ 5,61·10⁻⁴`); 4 pares com `s < 0,01`.
- Gram: intervalos com 0, 1, 2, 3 e 4 zeros: 307 766, 1 442 949, 299 567, 4 098 e 1; 20,66% de pontos de Gram ruins.
  O intervalo com 4 zeros é `[g_{12363155349036}, g_{12363155349037})`, zeros …349 037 a …349 040, em
  `t ≈ 3 000 175 779 509,21` a `509,44`.
- Rosser: 88 exceções. Cada uma é um par de blocos vizinhos, um com excesso e outro com falta (`Gram.bloco_par`).
- `S(t)`: máximo 2,326 logo depois do zero 12 363 154 829 321 (`t ≈ 3 000 175 658 078,709`); mínimo −2,226 logo
  antes do zero 12 363 154 660 798 (`t ≈ 3 000 175 618 704,687`); desvio-padrão 0,393.

**Pares mais frágeis** (`λ` de Csordas–Smith–Varga em `x = 2γ`, com `g` pela faixa mais a cauda pela densidade;
estimativa fora do kernel):

| zeros | `t` | `Δγ` | `s` | `Δ²g` | `λ_CSV` |
|---|---|---|---|---|---|
| 12 363 153 756 750/751 | 3 000 175 407 476,4146 | `9,585·10⁻⁴` | 0,0041 | `4,98·10⁻⁵` | `−4,59·10⁻⁷` |
| 12 363 153 570 515/516 | 3 000 175 363 963,2429 | `2,058·10⁻³` | 0,0088 | `3,93·10⁻⁴` | `−2,12·10⁻⁶` |
| 12 363 153 873 626/627 | 3 000 175 434 784,3130 | `2,166·10⁻³` | 0,0093 | `3,52·10⁻⁴` | `−2,35·10⁻⁶` |
| 12 363 155 255 037/038 | 3 000 175 757 546,3725 | `2,182·10⁻³` | 0,0093 | `3,40·10⁻⁴` | `−2,38·10⁻⁶` |
| 12 363 154 627 231/232 | 3 000 175 610 861,4975 | `2,562·10⁻³` | 0,0110 | `3,43·10⁻⁴` | `−3,28·10⁻⁶` |

O primeiro par está 8,3 vezes mais próximo que o par 694/695 da seção 13 (`Δγ = 0,007987`), e seu `λ` é cerca de 70
vezes menor em módulo. Para 2,05 milhões de espaçamentos do GUE, o mínimo típico é `≈ 0,0076` e a chance de algum
`s < 0,0041` é `≈ 14%`: não é anomalia.

No kernel, os teoremas desta faixa estão em `ClayRiemannProof/Continuacao.lean` (seção 26:
`JanelaContinuacao2026` como hipótese nomeada, `rhAteZ_continuacao`, `primeiro_fora_acima_continuacao`,
`par_mais_fragil_continuacao` com `−5,75·10⁻⁷ ≤ λ ≤ −4,59·10⁻⁷`) e em `Leis.fora_ate_continuacao_vazio`
(`{s ∈ Fora | |Im s| ≤ 3 000 175 822 471} = ∅`, condicional às mesmas três verificações).

**A próxima execução** começa onde esta terminou: `inicio.json` tem `C0 = 3 000 175 822 471,5` e
`N(C0) = 12 363 155 532 914`, e a faixa 0 recalcula esse `N` para colar. Resultados em `resultados-continuacao/de_<C0>/`.

**A segunda extensão: 16 faixas, até 3 000 177 742 471,5** (runs 41632268598 e 41652868086; branch
`resultados-continuacao`, pastas `de_3000175822471.5/` e `de_3000175822471.5/faixas_4-15/`; colagem conjunta em
`de_3000175822471.5/juntas_0-15/`). As faixas 0 a 15, de 120 000 unidades cada, cobrem
`3 000 175 822 471,5 < Im s ≤ 3 000 177 742 471,5` com **8 217 533 zeros, todos na reta**. `N(T)` é exato nas 17
pontas (`N(3 000 177 742 471,5) = 12 363 163 750 447`), as 16 colagens conferem (inclusive a 3→4, entre os dois runs)
e o déficit é 0 em cada faixa. Com Platt–Trudgian, a seção 13 e a primeira extensão, isso é RH conferida até
**3 000 177 742 471,5**: 2 409 671,5 unidades e 10 313 309 zeros acima do recorde publicado (3 000 175 332 800).
É cálculo certificado com aritmética intervalar, não verificação publicada. No kernel, com as janelas como
hipóteses nomeadas: `Continuacao.rhAteZ_continuacao2` e `Continuacao.primeiro_fora_acima_continuacao2` (branch
`continuacao-0-15`, aguardando o CI do Lean).

O par mais frágil das 16 faixas é o mais perto da colisão em todos os dados: zeros 12 363 161 233 435/…436
(`γ ≈ 3 000 177 154 379,729`), a 0,00073130 um do outro, `s = 0,0031`, `λ = −2,674·10⁻⁷`. Ele bate o da primeira
extensão (`−4,59·10⁻⁷`). No kernel: `−3,35·10⁻⁷ ≤ λ ≤ −2,67·10⁻⁷` (`Continuacao.par_mais_fragil_continuacao2`).
As faixas 16–23 e 24–35, a partir do mesmo `C0`, estão rodando.

**O que NÃO é**: uma verificação finita, que não diz nada sobre alturas maiores. O kernel não refaz o cálculo da Arb:
ele entra como hipótese nomeada. `λ` de um par de Lehmer é cota inferior para a constante de de Bruijn–Newman `Λ`
(teorema de Csordas–Smith–Varga, fora do kernel), mas Rodgers–Tao provaram `Λ ≥ 0`, e por pares de Lehmer já se tinha
`Λ > −1,1·10⁻¹¹` (Saouter–Gourdon–Demichel, 2011): estes pares não melhoram nada sobre `Λ`. `OPEN_MATH = true`.

## 32. As correções no kernel: cada afirmação errada dos gráficos, com o teorema que a decide

Arquivo: `ClayRiemannProof/Correcoes.lean`.

Os textos e gráficos colados em 3/11/2026 traziam afirmações sobre como um zero fora da reta apareceria, quanto um
par precisaria ser empurrado e onde estaria o fechamento. Cada uma está abaixo, com o enunciado correto e o teorema.

| afirmação | correto | teorema |
|---|---|---|
| um quarteto faz `S` saltar −2 | um par `ρ, 1 − ρ̄` sozinho numa janela conta 2 em `N` e 0 na reta (déficit exatamente 2); `S` **sobe**, entre 0 e 2 | `par_fora_na_janela`, `S_sobe_no_par`; `Leis.fora_em_pares`, `Leis.deficit_ao_menos_dois`, `Paridade.furo_de_dois` |
| `N` na caixa `[0,51; 0,99]` seria 1 | com `b < 0,01`, nenhum dos dois zeros do par está na caixa | `par_fora_da_caixa` |
| o par #6 forçado tem `b = 0,00245` em `λ = −3,19·10⁻⁵` | na colisão `b = 0` | `b_na_colisao`, `par6_valores_errados` |
| `b = 0,00678` em `λ = 10⁻⁴` | `b(−5·10⁻⁵) ∈ (0,0030; 0,0031)`, `b(−10⁻⁴) ∈ (0,0058; 0,0059)`, `b(−2·10⁻⁴) ∈ (0,0091; 0,0092)` | `par6_forcado`, `bForcado_eh_desvio` |
| a escala de fechamento é `Λ → 0⁻` | com Rodgers–Tao, `Λ < 0` é impossível e RH ⟺ `Λ = 0` | `lambda_negativo_impossivel`, `rh_iff_lambda_zero` |
| o par #6 "precisa só de 10⁻⁵ de força" para fechar | qualquer `λ < 0` de par de Lehmer é estritamente mais fraco que `Λ ≥ 0` | `cota_de_lehmer_mais_fraca` |
| Gram triplo é `Z` roçando 0 sem cruzar | 3 zeros num intervalo são 3 trocas de sinal; `j` zeros fazem `S` subir `j − 1` | `gram_k_zeros`, `Leis.gram_triplo`, `gram_quadruplo` |
| — (lacuna) | `JanelaContinuacao2026` sai das quatro contagens exatas da Arb e da fatia da seção 13 | `continuacao_de_contagens`, `janelaContinuacao_de_contagens`, `rhAteZ_de_contagens` |

**Correções que são de dados, não de teorema** (fonte: as listas certificadas das seções 13 e 31):
- `⟨δ⟩ = 2π/log(T/2π)`: 0,2337 em `3·10¹²`, 0,2067 em `10¹⁴`, 0,1795 em `10¹⁶`, 0,1287 em `10²²` (não 0,118).
- A fração de espaçamentos com `s < 0,08` é `5,30·10⁻⁴` em 2,05 milhões de zeros (GUE `≈ 5,61·10⁻⁴`), não
  `14/41 393 = 3,4·10⁻⁴`. As contagens "esperadas até `10²²`" são médias estatísticas, não candidatos a quarteto.
- A frequência não é "a cada ~500/690 em `t`, independente de `T`": em número de zeros ela é quase constante; em `t`
  ela escala com `2π/log(T/2π)`. As exceções de Rosser crescem com `T`: 1 em 41 393 zeros na seção 13, 88 em
  2 054 383 (1 a cada ~23 000) na seção 31.
- `0,006262 < β < 0,993738` em `3·10¹²` é a região **ainda permitida** pela região sem zeros explícita
  (`1 − 1/(5,5587 log t)`), não uma "região livre"; e até `3 000 175 822 471,5` tudo já está na reta.
- Análogos fora da reta: Davenport–Heilbronn `0,808517 + 85,699348i` e `ζ(s) + ζ(s + 1)` em
  `0,0988845 + 14,1534792i` conferem (`mpmath`, `|f| ≈ 5·10⁻³²`). "Epstein `0,65 + 100i`" e "Ihara `0,25 + 20i`" não
  existem. O zero de Epstein conferido (forma `m² + 5n²`) é `0,932970 + 15,668250i` (seção 19). Num grafo
  `(q+1)`-regular a adjacência é simétrica, logo seus autovalores `l` são reais, e fora do círculo os zeros de Ihara
  ficam no eixo real (`Analogs.ihara_fora_real`).
- As curvas "P fechar" não têm modelo de probabilidade por trás. O painel de Li não foi calculado.
- `Λ ≤ 0,1787854` (atribuído a um blog) não foi verificado; o provado é `Λ ≤ 0,2` (seção 12).

**Auditoria do repositório** (3/11/2026, refeita depois do rebase sobre `Alturas`, `Forca` e `Empurrao`): os 68 arquivos
`.lean` são alcançados pela raiz; nenhum `sorry`, `admit`,
`axiom` ou `native_decide`; todas as referências `Módulo.nome` do README existem; todo teorema tem guarda, depois de
corrigir uma guarda duplicada (`Leis.colisao_em_gama` no lugar de `Leis.colisao_em_gama'`).

**O que NÃO é**: as correções não aproximam nem afastam RH; dizem só o que cada número significa. `OPEN_MATH = true`.
**Axiomas**: `[propext, Classical.choice, Quot.sound]` (20 guardas, mais a de `PrimeiroFora.JanelaArb2026`).

## 33. Como os zeros se comportariam em alturas gigantes: só as leis que dependem de `ln T`

Arquivos: `computations/gigantes/gigantes.py` e `gigantes.json` (`mpmath`, 40 dígitos).

Acima de `8,1·10³⁴` (a maior altura em que já se calculou `Z(t)`, Bober–Hiary) nenhum zero pode ser calculado: em
`T = 10^100000` um único valor de `Z(t)` pede `10^50000` termos de Riemann–Siegel, ou `10^30769` operações pelo
algoritmo de Hiary. O que se sabe nessas alturas sai de leis que dependem de `T` só por `L = ln T`:

| altura `T` | `log₁₀ N(T)` | espaçamento médio | cota de `\|S(T)\|` | `S` típico | largura sem zeros `w` | `s` mínimo (GUE) | `λ` do par mais frágil | termos de R–S |
|---|---|---|---|---|---|---|---|---|
| 3·10¹² (faixa contígua certificada) | 13.09212933 | 0.233647 | 6.86209 | 0.4124 | 0.006262 | 4.194e-5 | −4.801e-11 | 6.91e5 |
| 10¹⁸ (Fronteira, 1ª onda) | 18.7885048 | 0.158632 | 8.32942 | 0.4344 | 0.00434 | 5.294e-7 | −3.527e-15 | 3.989e8 |
| 10²³ (Odlyzko) | 23.90184489 | 0.122907 | 9.64014 | 0.4484 | 0.003397 | 1.046e-8 | −8.258e-19 | 1.262e11 |
| 8,1·10³⁴ (Bober–Hiary, maior altura calculada) | 35.99984148 | 0.0799979 | 12.7279 | 0.4714 | 0.002238 | 9.698e-13 | −3.01e-27 | 1.135e17 |
| 10¹⁰⁰ (googol) | 101.55865 | 0.0275071 | 29.3545 | 0.5249 | 0.0007813 | 1.361e-34 | −7.005e-72 | 3.989e49 |
| 3^100000 | 47716.36813 | 5.7193e-5 | 11414.9 | 0.7668 | 3.486e-6 | 3.393e-15906 | −1.883e-31820 | 4.609e23855 |
| 10^100000 | 100004.564 | 2.72877e-5 | 23912.4 | 0.7909 | 2.085e-6 | 1.355e-33335 | −6.837e-66680 | 3.989e49999 |
| 2^1000000 | 301035.0383 | 9.06474e-6 | 71960.5 | 0.8254 | 9.719e-7 | 9.416e-100346 | −3.643e-200701 | 3.97e150514 |
| 10^(10¹⁴) | 1.0e+14 | 2.72875e-14 | 2.39008e+13 | 1.294 | 1.501e-12 | 1.355e-33333333333338 | −6.837e-66666666666704 | 3.989e49999999999999 |
| 10^(10¹⁰⁰) (googolplex) | 1.0e+100 | 2.72875e-100 | 2.39008e+99 | 3.422 | 3.645e-70 | 10^(-3.33333e+99) | −10^(-6.66667e+99) | 10^(5.0e+99) |
| 10↑↑4 = 10^10^10^10 | 1.0e+10000000000 | 2.72875e-10000000000 | 2.39008e+9999999999 | 3.415e+4 | 7.862e-6666666673 | 10^(-3.33333e+9999999999) | −10^(-6.66667e+9999999999) | 10^(5.0e+9999999999) |

- **Contagem**: `N(T) = (T/2π)(ln(T/2π) − 1) + 7/8 + S(T) + O(1/T)`, com `|S(T)| ≤ 0,1038 L + 0,2573 ln L + 8,3675`
  (Hasanalizade–Shen–Wong 2021). Em `10^(10¹⁴)` isso deixa `N` com incerteza de `±2,4·10¹³` zeros: sem calcular
  zeros, não há déficit para medir.
- **Espaçamento**: `⟨δ⟩ = 2π/ln(T/2π)` encolhe como `1/L`. Em unidades normalizadas (`s = Δγ/⟨δ⟩`) a estatística é a
  mesma (GUE: conjectura de Montgomery–Odlyzko, conferida até `10²³`).
- **`S(t)` cresce**: o tamanho típico `√(ln L/(2π²))` passa de 0,41 em `3·10¹²` a 3,4 no googolplex, e
  `|S| = Ω((ln T)^{1/3}(ln ln T)^{−1/3})` sem hipótese (Tsang). A lei de Gram falha cada vez mais e a regra de Rosser
  falha infinitas vezes (Lehman 1970): o método de Turing continua valendo, os atalhos de Gram e Rosser não.
- **Onde um zero fora da reta poderia estar**: em `w < β < 1 − w`, com `w` da região sem zeros
  (Mossinghoff–Trudgian–Yang 2022: `1/(5,558691 L)` clássica, `1/(55,241 L^{2/3}(ln L)^{1/3})` de Korobov–Vinogradov,
  esta a mais larga para `T > e^52238`). Em `10^100000`, `w = 2,1·10⁻⁶`: nada exclui um zero com `b` até
  `0,499998`. As estimativas de densidade (`N(σ, T) ≪ T^{1 − (σ − ½)/4} ln T`, Selberg) dizem só que zeros longe da reta
  seriam uma fração que vai a 0, sem constante explícita.
- **Os pares ficam cada vez mais frágeis**: o par mais próximo entre os `N(T)` zeros tem `s ≈ (9/(π²N))^{1/3}`
  (GUE) e colide no fluxo de de Bruijn em `λ ≈ −Δγ²/2`. Em `3·10¹²` isso dá `−4,8·10⁻¹¹` (o recorde publicado por
  pares de Lehmer é `−1,1·10⁻¹¹`, Saouter–Gourdon–Demichel 2011); em `10^100000`, `−6,8·10⁻⁶⁶⁶⁸⁰`. É o mecanismo do
  teorema de Rodgers–Tao (`Λ ≥ 0`): se `Λ` fosse negativo, os zeros altos teriam de ser regulares demais. Pares frágeis
  não indicam zeros fora da reta (`Correcoes.cota_de_lehmer_mais_fraca`).

**Só acima do verificado** (`acima.py`, `figura_acima.py`, `acima.png`): de `10¹⁹` ao googolplex, sem repetir nada
do que já foi conferido.

![acima do verificado](computations/gigantes/acima.png)

- O par mais frágil esperado entre os zeros até `T` (GUE) tem `|λ| ≈ 10^−15,2` em `10¹⁹`, `10^−71` em `10¹⁰⁰` e
  `10^−66 679` em `10^100000`.
- Pares mais frágeis que o recorde já visto (`λ < −4,59·10⁻⁷`) aparecem em média a cada `5,3·10⁵` de altura em
  `10¹⁹`, a cada 600 em `10¹⁰⁰`; acima de `3^100000` o espaçamento médio já é menor que o do recorde e praticamente
  todo par é mais frágil que ele.
- A região sem zeros exclui só `w = 0,0041` em `10¹⁹`, `7,8·10⁻⁴` em `10¹⁰⁰`, `2,1·10⁻⁶` em `10^100000`: um zero fora
  da reta continua permitido em quase toda a faixa.

**O que NÃO é**: nenhum número desta tabela é um zero calculado nem uma verificação; são as leis e cotas conhecidas
avaliadas em `L = ln T`. A coluna GUE é heurística (modelo de matrizes aleatórias), não teorema. `OPEN_MATH = true`.

## 34. Aglomerações, e onde os zeros fora da reta existem ou chegam mais perto

Arquivos: `computations/aglomeracoes/` (`aglomeracoes.py`, `analogos_fora.py`, `figura.py`, os `.json` e
`aglomeracoes_e_fora_da_reta.png`).

![aglomerações e zeros fora da reta](computations/aglomeracoes/aglomeracoes_e_fora_da_reta.png)

- **Fora da reta de verdade só sem produto de Euler** (painel a; `mpmath`, malha e `findroot`, `|f| < 10⁻³⁰`):
  - Davenport–Heilbronn até `Im 170`: 3 zeros, `0,808517 + 85,699348i` (`b = 0,3085`), `0,650830 + 114,163343i`
    (`b = 0,1508`), `0,574356 + 166,479306i` (`b = 0,0744`), mais os espelhos `1 − β + iγ`;
  - Epstein `m² + 5n²` até `Im 100`: 12, de `b = 0,0974` a `b = 0,4377` (`0,937667 + 29,983395i`);
  - `ζ(s) + ζ(s + 1)` até `Im 100`: 28, todos com `0,099 ≤ Re ≤ 0,275` (não tem equação funcional);
  - `ζ`: os 64 zeros até `Im 170` estão em `Re = ½`.
- **Onde `ζ` chega mais perto de sair** (painel b): o par mais frágil de cada janela certificada (9,9 milhões de zeros:
  seção 13, seção 31 e as 16 varreduras da Fronteira de `10¹³` a `10¹⁸`). O mais perto de colidir de todos é o par
  12 363 153 756 750/751 da seção 31 (`λ = −4,59·10⁻⁷`); depois `10¹⁴` (`−5,54·10⁻⁷`) e `10¹⁶` (`−7,79·10⁻⁷`).
  Nenhum saiu da reta: déficit 0 em todas as janelas.
- **A aglomeração mais densa** (painel c): 7 zeros em 3,66 espaçamentos médios a partir de
  `t = 3000175458815,17891772…`, com o par 12363153976477/478 (`s = 0,029`,
  `λ = -2,31e-05`), o mais fácil de empurrar até o quarteto `b = 0,2` (seção 28). `S` sobe 1 em
  cada zero e desce entre eles.
- **Aglomerações são limitadas** (painel d): numa janela de 4 espaçamentos médios há no máximo 7 zeros (71 janelas
  em 2 054 383); pontos ao acaso dariam 8 ou mais em 5,1% das janelas. O maior vazio tem `s = 3,44`, e `S`
  cai de 1,97 a -1,46 nele.

**O que NÃO é**: as funções do painel (a) não são `ζ`; mostram que sem produto de Euler a reta não segura os zeros.
Os pares do painel (b) são aproximações de uma colisão no fluxo de de Bruijn (`t < 0`), não zeros fora da reta.
`OPEN_MATH = true`.

## 35. As alturas 10⁵⁰, 10¹⁰⁰, 10²⁵⁷, 10⁵⁵⁷ e 10¹⁰⁰⁰ medidas: o produto de Euler, a matriz aleatória calibrada e onde ζ é mais fraca

Arquivos: `computations/gigantes/` (`euler.py`, `valida.py`, `valida_alturas.py`, `cue.py`, `varre_euler.py`,
`confere.py`, `resumo.py`; resultados em `computations/gigantes/resultados/`). Complementa a seção 33 (as leis que
dependem só de `ln T`): aqui entram o que se mede nessas alturas e o modelo calibrado nos dados.

**Nessas alturas ninguém calcula zeros.** Um único valor de `Z(t)` em `10⁵⁰` pede `10^24,6` termos de
Riemann–Siegel. Pelo algoritmo de Hiary (`T^{1/3}`, o melhor implementado), com a constante calibrada no recorde de
Bober–Hiary (`t ≈ 8,1·10³⁴`, 22,5 anos-núcleo), um valor custaria `2·10⁶` anos-núcleo em `10⁵⁰`, `10²³` em `10¹⁰⁰`,
`10⁷⁵` em `10²⁵⁷`, `10¹⁷⁵` em `10⁵⁵⁷` e `10³²³` em `10¹⁰⁰⁰`. O que roda está em três camadas, e cada uma tem o seu nome
abaixo.

**1. O que é teorema e conta exata** (seção 33 para as outras alturas). Pela cota de Hasanalizade–Shen–Wong
(Corolário 1.2: `|N(T) − (T/2π)log(T/2πe)| ≤ 0,1038 log T + 0,2573 log log T + 9,3675`), `N(10¹⁰⁰⁰)` tem 1 003
algarismos (começa por 36 601 613 727 670 769 617…) e fica determinado a menos de ±250. `N(10⁵⁰)` tem 52 algarismos
(17 871 727 808 979 519 260…), a menos de ±23.

**2. O que se mede: o produto de Euler.** O fator aritmético de `ζ` na reta é
`P_X(t) = Π_{p ≤ X}(1 − p^{−1/2−it})^{−1}`. As fases `t·log p mod 2π` foram calculadas exatamente, com o expoente mais
40 algarismos (1 040 em `10¹⁰⁰⁰`). Antes de usar o produto nas alturas gigantes, testei se ele prevê o que medimos:

* Nas 41 392 lombadas de `3·10¹²` (seção 28), `log|P_X|` no extremo tem correlação **0,89** com `log|Z*|`
  (`X = 10⁴`; 0,60 com `X = 10`, 0,75 com 100, 0,83 com 1 000). No 1% das lombadas com o menor `P_X`, a mediana de
  `|Z*|` é 0,079, contra 1,44 no total, e 58% delas ficam abaixo de 0,1, contra 3,4% no total (17 vezes mais). As 100
  lombadas mais baixas têm `P_X` no percentil mediano 2,4%. Resumindo: o produto acha onde estão as lombadas baixas,
  que são os pares mais fáceis de tirar da reta por empurrão.
* Para os pares mais apertados ele acerta menos. Nas janelas certificadas de `10¹⁴`, `10¹⁶` e `10¹⁷` (seção 18), a
  correlação de `log s` com `log|P_X|` é 0,49, 0,43 e 0,40, e os 100 pares mais apertados têm `P_X` no percentil
  mediano 19, 30 e 25. O par de `10¹⁶` com `s = 0,0078` fica no percentil 41. Isso é a lei empírica 7 de novo: o
  empurrão e o calor escolhem pontos diferentes, e o produto de Euler enxerga o empurrão.

Nas alturas gigantes, varri `P_X` (`X = 10⁵`, 9 592 primos; `varre_euler.py`) na janela `10^k ≤ t ≤ 10^k + 200`, com malha 0,004 (o
produto varia na escala `1/log X ≈ 0,09`). Os vales mais fundos são onde a parte aritmética de `ζ` é mais fraca. O
valor de `log|P_X|` em cada vale foi conferido por outro caminho (`confere.py`: fases calculadas direto em `t*`, sem
a soma `fase(10^k) + u·log p`), e a diferença ficou abaixo de `10⁻¹³`:

| altura | vale mais fundo (± 0,004) | `log|P_X|` no vale | desvios abaixo da média | 2º vale |
|---|---|---|---|---|
| 10⁵⁰ | `10⁵⁰ + 7,388` | −4,04 | 3,4 | `10⁵⁰ + 197,720` (−3,21) |
| 10¹⁰⁰ | `10¹⁰⁰ + 74,616` | −3,37 | 2,8 | `10¹⁰⁰ + 164,160` (−3,07) |
| 10²⁵⁷ | `10²⁵⁷ + 176,920` | −4,05 | 3,4 | `10²⁵⁷ + 114,040` (−3,24) |
| 10⁵⁵⁷ | `10⁵⁵⁷ + 56,696` | −3,49 | 2,9 | `10⁵⁵⁷ + 147,212` (−3,48) |
| 10¹⁰⁰⁰ | `10¹⁰⁰⁰ + 62,308` | −3,83 | 3,2 | `10¹⁰⁰⁰ + 153,144` (−3,45) |

Em `3·10¹²` o vale a −3,4 desvios estaria no 0,03% mais baixo, onde as lombadas abaixo de 0,1 são a maioria. Nas
alturas gigantes o produto explica uma parte menor da variação de `log|ζ|`: o desvio de `log|P_X|` fica em 1,19 em
todas, e a variância de `log|ζ|` cresce como `½ log log T`. A concentração continua, só que mais fraca. São os pontos
por onde começar, se um dia for possível calcular `ζ` ali. Não dá para conferir se há uma lombada baixa em cada um.

**3. O que o modelo diz: a matriz aleatória do tamanho certo.** Pelo modelo de Keating–Snaith, na altura `T` a função
`ζ(½ + it)` se comporta como o polinômio característico de uma matriz unitária aleatória (CUE) de tamanho
`N = log(T/2π)`. O análogo de `Z` é `Z_U(θ) = Π 2 sen((θ − θ_j)/2)`, e as lombadas ficam entre autoângulos
consecutivos (`cue.py`). **Calibração com os dados**: com `N = 27` (o tamanho de `3·10¹²`, 108 000 lombadas
simuladas), a fração de lombadas abaixo de cada `ε` é 0,17% (`ε = 0,01`; medido 0,16%), 4,0% (0,1; medido 3,4%), 14,8%
(0,32; 13,7%), **39,2%** (1; 39%), 56,0% (1,78; 57%), 72,5% (3,16; 73%), **85,7%** (5,6; 86%), 94,0% (10; 94%) e
99,5% (31,6; 99,4%). A mediana é 1,455, contra 1,43 medida. O modelo lognormal com a variância de Selberg dava 46% e
90%; o CUE acerta a menos de um ponto. Ele erra na cauda: prevê a lombada mínima cerca de 2 vezes mais baixa que a
medida (4,9·10⁻⁴ contra 1,03·10⁻³ em 41 393 zeros, 3,1·10⁻⁵ contra 5,3·10⁻⁵ em 2 095 776).

| altura | `N` do CUE | lombada mediana | var. de `log` lombada | tirados da reta com `ε = 1` | com `ε` = média quadrática | lombada mínima em 10⁴ zeros | em 10⁶ | `λ` do par mais apertado em 10⁴ zeros |
|---|---|---|---|---|---|---|---|---|
| 3·10¹² | 27 | 1,45 | 1,92 | 39% | 84,6% | 1,4·10⁻³ | 5,4·10⁻⁵ | −5,5·10⁻⁵ |
| 10⁵⁰ | 113 | 1,40 | 2,66 | 42% | 90,6% | 6,4·10⁻⁴ | 2,0·10⁻⁵ | −3,1·10⁻⁶ |
| 10¹⁰⁰ | 228 | 1,40 | 3,02 | 42% | 92,6% | 5,4·10⁻⁴ | 1,6·10⁻⁵ | −7,7·10⁻⁷ |
| 10²⁵⁷ | 590 | 1,38 | 3,41 | 43% | 94,8% | 3,5·10⁻⁴ | 8,8·10⁻⁶ | −1,1·10⁻⁷ |
| 10⁵⁵⁷ | 1 281 | 1,34 | 3,93 | 44% | 95,5% | 2,7·10⁻⁴ | 6,6·10⁻⁶ | −2,4·10⁻⁸ |
| 10¹⁰⁰⁰ | 2 301 | 1,37 | 4,24 | 44% | 96,2% | 2,1·10⁻⁴ | 4,7·10⁻⁶ | −7,6·10⁻⁹ |

**A leitura.**

* **A mediana não sai do lugar.** A lombada mediana fica em torno de 1,4 em todas as alturas. O que cresce é a
  largura: a variância de `log` lombada vai de 1,9 a 4,2.
* **Empurrão relativo e empurrão fixo.** Um empurrão do tamanho da média quadrática tira da reta 85% dos pares em
  `3·10¹²` e 96% em `10¹⁰⁰⁰`. Um empurrão fixo `ε = 1` tira de 39% a 44%.
* **Força mínima.** Para tirar o primeiro par da reta numa janela de 10⁴ zeros, a força necessária cai 7 vezes entre
  `3·10¹²` e `10¹⁰⁰⁰`.
* **Tempo do calor.** O `λ` do par mais apertado chega 7 000 vezes mais perto de `0⁻`, porque a densidade cresce como
  `log T`.

Pelo modelo, quanto mais alto, mais perto da colisão os zeros ficam. É o que Rodgers–Tao provaram (`Λ ≥ 0`): `ζ` está
na borda. Nada disso põe um zero fora da reta. `OPEN_MATH = true`.

**O que é cada coisa.** A cota de `N(T)` e o ponto de Gram são teoremas mais conta exata. `P_X` é medido e conferido
nos dados (r = 0,89). A tabela do CUE é modelo, calibrado nos dados de `3·10¹²` (a menos de um ponto no meio da
distribuição e um fator 2 na cauda). Os vales são onde o modelo híbrido de Gonek–Hughes–Keating põe as lombadas
baixas, não zeros achados.
**Origem**: Keating–Snaith (2000), Gonek–Hughes–Keating (2007), Hasanalizade–Shen–Wong (2022), Hiary (2011),
Bober–Hiary (2018), Rodgers–Tao (2020); a validação do produto de Euler nas lombadas medidas e a calibração do CUE
contra elas são novas.

## Autor

Tiago Paschoalatto Fagliari (ShantiDraconis) — ORCID [0009-0006-6874-3910](https://orcid.org/0009-0006-6874-3910).
Como citar: `CITATION.cff`. Licença: CC0 1.0 (domínio público), `LICENSE`.
