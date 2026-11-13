# Reivindicações

O que este repositório reivindica, item por item, com o certificado de cada um. Data: 13/11/2026.

**Autor**: Tiago Paschoalatto Fagliari (ShantiDraconis), ORCID
[0009-0006-6874-3910](https://orcid.org/0009-0006-6874-3910). Licença CC0 1.0. Como citar: `CITATION.cff`.

## Regra

Só se reivindica o que tem certificado:

- **(K) kernel**: conferido pelo Lean 4 (v4.36.0-rc2, Mathlib `8fe7ce4`), sem `sorry`, `axiom`, `native_decide` ou
  marcador, com a saída de `#print axioms` fixada por `#guard_msgs` em `ClayRiemannProof/Audit.lean`: no máximo
  `[propext, Classical.choice, Quot.sound]`.
- **(C) cálculo certificado**: aritmética intervalar fora do kernel, com execução e arquivos públicos.
- **(N) numérico**: ponto flutuante fora do kernel, com o script público; vale como medida, não como prova.

Cada item tem uma classe:

- **reformulação**: enunciado equivalente a um já conhecido; o que é do autor é a formulação, não um resultado novo;
- **consequência**: segue de resultados conhecidos;
- **ferramenta**: resultado conhecido, formalizado aqui;
- **refutação**: proposta recusada no kernel, com o contraexemplo ou a contradição;
- **condicional**: implicação a partir de uma hipótese nomeada (`def … : Prop`, nunca `axiom`).

**Novo**: nenhum item está marcado como novo. Marcar exige uma proposta com o enunciado e a referência que mostre que
ele não está na literatura, e o aceite do autor. Proposta aberta, aguardando decisão:
[#4](https://github.com/ShantiDraconis/clay-riemann-proof/issues/4), a continuação contígua até `3 000 209 302 471,5`
(§3 abaixo). Os demais itens não são candidatos: são reformulações, consequências ou formalizações de resultados
conhecidos.

## O que NÃO se reivindica

- **A Hipótese de Riemann.** `OPEN_MATH = true`. Nada aqui a prova ou a refuta.
- **Nenhum prêmio.** O Clay e a AMS só consideram solução publicada em periódico referado; o Clay espera ainda dois
  anos e aceitação geral. A formalização é material suplementar.
- **Resultados externos.** Platt–Trudgian (2021), o quasi-RH anunciado pela OpenAI (06/10/2026), de la Vallée Poussin
  (1899), Hardy (1914) e o critério de Weil entram só como hipóteses nomeadas. Não são verificados aqui.

## 1. Eixo Riemann (§66; `ClayRiemannProof/EixoRiemann/`, 205 teoremas, todos com guarda)

### Reformulações (K)

| Enunciado | Teorema |
|---|---|
| RH ⟺ `RHFaixa` ⟺ `RHIdem` ⟺ `RHQuarteto` ⟺ nenhuma ponte horizontal ⟺ `RHF` | `rh_eixo_riemann` |
| RH ⟺ não existe ponte `z → z + δ`, `δ` real `≠ 0`, entre zeros da faixa | `rh_iff_sem_ponte_horizontal` |
| RH ⟺ RH no eixo `Idem` corrigida (`Re z = 1/2`, `Re δ = 0`) | `rhIdem_iff` |
| RH ⟺ existe a "projeção do espelho" (autovalor `1/(1 + 4δ²)` em cada zero) | `projecao_iff_rh` |
| RH ⟺ `S(φ) = c²` | `somaDeQuadrados_iff` |
| todo zero da faixa tem `Re ≤ θ` ⟺ toda ponte horizontal tem `|δ| ≤ 2θ − 1` | `quase_rh_iff_pontes` |
| a "RH-Dual" é a conjectura dos zeros simples, não RH | `rhDual_iff_zerosSimples` |

### Consequências incondicionais (K)

| Enunciado | Teorema |
|---|---|
| dois quartetos `{s, s̄, 1 − s, 1 − s̄}` com um ponto em comum são o mesmo | `orbitas_iguais_ou_disjuntas` |
| fora da reta e do eixo real o quarteto tem 4 pontos, 2 com `Im > 0` | `orbita_card`, `orbita_metade_de_cima` |
| todo conjunto finito simétrico de zeros fora da reta tem `4k` pontos | `quartetos_geral`, `zeros_fora_em_quartetos` |
| o grupo de Klein age em `ℂ⁴` e `Q(s)` comuta com ele (o quarteto como operador) | `Q_espelho`, `Q_tensao`, `Q_torcao` |
| zero fora da reta `ρ` ⟹ ponte horizontal `ρ → 1 − ρ̄`, `δ = 1 − 2 Re ρ` | `ponte_horizontal_do_quarteto` |
| toda ponte horizontal na faixa tem `|δ| < 1`; numa janela são finitas e em número par | `ponte_horizontal_curta`, `pontes_horizontais_finitas_e_pares` |
| nenhuma multiplicação associativa com unidade em `ℝ³` tem elemento com quadrado `−1` | `sem_raiz_de_menos_um_dim3`, `sem_algebra_associativa_dim3` |
| `Idem = ℂ[e]/(e² − e)` tem exatamente 4 idempotentes | `Idem.idempotentes` |
| ponte habitada fora da faixa: `ζ(−2 + (−2)e) = (0, 0)` | `Idem.trivial_carrega_trivial`, `habitante_ponte_nao_trivial` |
| nenhuma família finita de desigualdades estritas contínuas separa `ζ` dos falsos zetas próximos | `familia_finita_estrita_nao_basta`, `modelo_beta` |
| em `Prop` não há valor intermediário; RH é `0` ou `1` | `meio_tercio_excluido`, `rh_nao_e_meio` |
| Łukasiewicz com `m + 1` valores: a negação tem ponto fixo ⟺ `m` par, e o fixo é `1/2` | `lukasiewicz_fixo_iff` |
| a equação funcional vale para qualquer valor de `ζ(2k + 1)` | `equacao_funcional_cega_impar` |

### Condicionais (K)

| Hipótese ⟹ conclusão | Teorema |
|---|---|
| `ψ(x) − x = O(x^θ)`, `θ ≥ 0` ⟹ `ζ(ρ) ≠ 0` para `Re ρ > θ` | `sem_zeros_acima`, `sem_zeros_acima_chebyshev` |
| o mesmo ⟹ toda ponte horizontal tem `|δ| ≤ 2θ − 1` | `controle_psi_pontes` |
| `ψ(x) − x = O(x^{1/2 + ε})` para todo `ε > 0` ⟹ RH | `rh_de_controle_psi`, `rh_de_chebyshev` |
| havendo um zero na faixa, nenhum `ψ(x) − x = O(x^θ)` com `0 ≤ θ < 1/2` | `controle_psi_abaixo_do_meio` |
| `ζ ≠ 0` em `Re s > σ₀` ⟹ `|δ| ≤ 2σ₀ − 1` | `pontes_de_semiplano` |
| quasi-RH `1/8–7/8` (OpenAI, hipótese nomeada `OpenAIQuasiRH78`) ⟹ `|δ| ≤ 3/4` | `semiplano_de_openai`, `pontes_openai_78` |
| `ζ ≠ 0` em `Re s > 11/12` ⟹ `|δ| ≤ 5/6` | `pontes_onze_doze` |
| região de de la Vallée Poussin ⟹ ponte na altura `t` tem `|δ| < 1 − 2c/log t` | `ponte_horizontal_dlvp` |
| Platt–Trudgian (2021) ⟹ toda ponte até `3 000 175 332 800` é vertical | `pontes_verticais_platt_trudgian` |
| critério de Weil ⟹ (RH no eixo ⟺ positividade) | `rhIdem_iff_weil`, `tronco_weil_rh` |

### Refutações (K)

| Proposta recusada | Teorema |
|---|---|
| a tabuada `a + bi + cR` (`R² = R`, `iR = R`) é associativa | `R3.nao_associativa` |
| "RH-Idem" com `δ = 0`: implicaria que `ζ` não tem zeros não triviais | `rhIdemProposta_implica_sem_zeros`, `hardy_refuta_rhIdemProposta` |
| quartetos "conectados" (um zero carregando 6, 8, 10, 12) | `inabitante_quarteto_conectado` |
| a "ponte de campo" | `ponteCampo_apaga_zeros`, `hardy_refuta_ponteCampo` |
| a escada de 5 valores proposta | `e5_nao_associativo` (não é associativa) |
| famílias de Gram linear e média sobre os primos | `gram_homogeneidade_no_go`, `gram_no_go`, `media_gram` |
| `min` como `∧` na codificação `0 = F, 1 = T, 2 = U` | `codA_quebra_min` |
| simetria do quarteto ⟹ zeros na reta | `simetria_nao_implica_reta` (contraexemplo `contraQ`) |

### Ferramentas (K; resultados conhecidos)

| Resultado | Teorema |
|---|---|
| `ψ(x) − x = O(x^θ)` ⟹ região sem zeros (clássico) | `sem_zeros_acima` |
| `3 + 4 cos θ + cos 2θ ≥ 0` e a positividade com `Λ(n)` | `tres_quatro_um`, `positividade_aritmetica` |
| `ζ(2k) = q·π^{2k}`, `q ∈ ℚ` (Euler) | `zeta_par_fecha` |
| `Σ_p p^{−σ}` converge ⟺ `σ > 1` | `cauda_primos_iff` |
| Riemann–Lebesgue: cada teste fixo é cego para alturas grandes | `teste_fixo_cego` |

### Numérico (N)

- Desigualdade de Weil finita na escala `log 4` (só os primos 2 e 3; o 4 cai na borda, onde `g = 0`), teste
  `g = h ∗ h̃`, `h` suave em `[−log 2, log 2]`: em `γ = 0`, polo `0,19305`, primo 2 `−0,02301`, primo 3 `−0,00060`,
  arquimediano `−0,16920`, **`W = 2,344·10⁻⁴ > 0`**; o lado dos zeros (138 zeros até `T = 300`) dá o mesmo valor com
  diferença `1,5·10⁻¹³`. `computations/eixo_riemann/weil_finito.py`.

## 2. Candidatos à Mathlib (K; `ClayRiemannProof/MathlibCandidates/`, só Mathlib)

| Teorema | Classe |
|---|---|
| `Chebyshev.riemannZeta_ne_zero_of_isBigO`: `ψ x − x = O(x^β)`, `0 ≤ β` ⟹ `ζ(s) ≠ 0` em `β < Re s` | ferramenta |
| `Complex.eventually_exists_zero_of_tendstoUniformlyOn` (Hurwitz, existência de zeros) | ferramenta |
| `Complex.im_eq_zero_of_tendstoLocallyUniformly` (limite de funções inteiras com zeros reais) | ferramenta |

Compilam no CI deste repositório. O PR na `leanprover-community/mathlib4` não é aberto por uma sessão de IA. A política
da Mathlib (https://leanprover-community.github.io/contribute/) exige que quem envia entenda todo o código escrito por IA
e justifique cada decisão sem IA, declare o uso de IA no PR (rótulo `LLM-generated`) e escreva os comentários com as
próprias palavras; PRs de baixa qualidade gerados por LLM são fechados e o autor pode ser suspenso. O PR fica para o
autor, depois de estudar a prova.

## 3. O restante do repositório (README §1–§65)

Cada seção do README diz o seu estatuto. As que reivindicam algo:

- **Equivalências (K)**: §1 Báez-Duarte (`target_iff_gap`); §5 `D_ω`; §6 bicomplexos; §21 as 22 formulações são a
  mesma proposição.
- **Teoremas (K)**: §3 aritméticas finitas; §4 nenhum zero de `ζ` na faixa até a altura 13; §9 Nyman–Beurling para
  `θ` real; §10; §14 Li sem Hadamard (forma finita); §17 unicidade por simetria; §47 o primeiro zero certificado na reta
  pelo kernel.
- **Condicionais (K)**: §2 RH sob o quasi-RH `1/8–7/8`; §20 zero fora da reta de altura mínima.
- **Cálculo certificado (C)**: §13 e §15 janelas acima de `3·10¹²`; §31 e `VALORES_FIXADOS.md`, a continuação
  contígua: **RH conferida até a altura `3 000 209 302 471,5`**, `N = 12 363 298 826 181`, 145 389 043 zeros acima de
  Platt–Trudgian (`T_PT = 3 000 175 332 800`), todos em `Re s = 1/2`. É extensão contígua da verificação publicada em
  33 969 671,5 unidades de altura, com FLINT 3 / Arb a 256 bits; não é revisada por pares. Pausada em 13/11/2026.
  Proposta de classe "novo": [#4](https://github.com/ShantiDraconis/clay-riemann-proof/issues/4), aguardando decisão.

## Como conferir

`lake build` (CI: `.github/workflows/lean.yml`). As guardas estão em `ClayRiemannProof/Audit.lean`,
`ClayRiemannProof/AuditThirteen.lean` e `ClayRiemannProof/MathlibCandidates/PsiZeroFree.lean`.
