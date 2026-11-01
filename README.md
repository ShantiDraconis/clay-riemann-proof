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
de `#print axioms` de cada uma das 297 declarações públicas acrescentadas. Todas dependem apenas de
`[propext, Classical.choice, Quot.sound]` (os axiomas padrão que o próprio Mathlib usa; `Real` já
depende deles). Verificado com Lean 4.36.0-rc2 e Mathlib `8fe7ce4`.

## Álgebra bicomplexa de coordenadas (suplementar; não prova RH)

Arquivo: `ClayRiemannProof/BicomplexCoordinates.lean`.

O módulo formaliza identidades de coordenadas: `i²=j²=-1`, `ij=ji=k`, `k²=1`,
`(1+k)(1-k)=0) com fatores não nulos, o inverso de `j`, e as contas de
`-1+i(a+ib)` versus `-1+i(a+jb)`. Também verifica que as coordenadas reais
dos componentes idempotentes são `σ+b` e `σ-b), ambas iguais a `σ) quando `b=0).

Aqui `a+ib` usa a unidade complexa ordinária: `-1+i(a+ib)=(-1-b)+ia`; isso não requer
uma extensão bicomplexa. Com uma unidade independente `j), `i(a+jb)=ia+kb), e o
coeficiente escalar real não muda. Zero-divisores são elementos não nulos cujo produto
pode ser zero; isso não torna um valor de função igual a zero quando apenas um componente
idempotente se anula.

Esta seção não define `ζ) sobre os bicomplexos e não implica que os zeros da zeta clássica
estejam ou não na linha crítica. A Hipótese de Riemann continua aberta neste repositório.

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

**Origem** (ATK kernel, espelho público do M-Core, `imports/M-Core/atk-kernel/ATK/`): detalhes omitidos.

## 2. RH condicional ao quasi-RH 1/8–7/8

Arquivo: `ClayRiemannProof/QuasiRH.lean`.

Este resultado é condicional a uma hipótese externa e não é uma prova de RH. Consulte o arquivo para o
enunciado formal e as dependências.

## 3. A ponte com as aritméticas finitas

Arquivos: `ClayRiemannProof/FiniteWorlds.lean` e `ClayRiemannProof/Zeta/Symmetry.lean`.

A formalização relaciona RH ao conjunto de todos os limites finitos; nenhum limite isolado prova RH.
Consulte os arquivos e `Audit.lean` para as declarações e dependências formais.
