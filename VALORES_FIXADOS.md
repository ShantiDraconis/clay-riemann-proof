# Valores fixados da continuação contígua

**Pausada em 13/11/2026 a pedido do autor.** Os valores abaixo estão fixados e não mudam até a continuação ser
retomada. Cada um aponta para o commit, a execução e os arquivos de onde sai.

Isto **não** é prova de RH (`OPEN_MATH = true`). É uma verificação numérica com aritmética intervalar (FLINT 3 / Arb,
256 bits), feita fora do kernel. No Lean ela entra como hipóteses nomeadas, uma por janela.

## Valor final

| | |
|---|---|
| RH conferida até a altura | **3 000 209 302 471,5** |
| `N(3 000 209 302 471,5)` | 12 363 298 826 181 (contagem de Turing intervalar, `acb_dirichlet_zeta_nzeros`) |
| recorde publicado (Platt–Trudgian 2021) | `T_PT = 3 000 175 332 800`, `N(T_PT) = 12 363 153 437 138` |
| acima do recorde | 33 969 671,5 unidades de altura e 145 389 043 zeros, todos em `Re s = ½`, déficit 0 em todas as colagens |
| maior raio das bolas | 5,01·10⁻¹⁸ |
| par mais perto em todos os dados | 12 363 187 982 787/…788 (`γ ≈ 3 000 183 404 278,7579`, distância 0,00036432, `s = 0,0016`, `λ = −6,636·10⁻⁸`) |
| no kernel | `ClayRiemannProof.Continuacao.rhAteZ_continuacao43 : … → RHateZ 3000209302471`, com 45 hipóteses nomeadas (`PlattTrudgian2021`, `JanelaArb2026`, `JanelaContinuacao2026` … `JanelaContinuacao2026aq`); axiomas `[propext, Classical.choice, Quot.sound]` (guarda em `Audit.lean`) |
| Lean e Mathlib | Lean 4.36.0-rc2, Mathlib `8fe7ce4`; 1 856 guardas `#guard_msgs` |
| commit do resultado | `main` em `1b6b252` (CI Lean 43401888535 verde); este arquivo e a tag `rh-conferida-3000209302471.5` no commit seguinte, que só mexe em documentação |
| dados | branch `resultados-continuacao` em `3ccf7e5` (tag `dados-continuacao-3000209302471.5`), junção final em `de_3000207862471.5/juntas_0-11/` |
| ponto de retomada | `computations/continuacao/inicio.json`: `C0 = 3000209302471.5`, `N(C0) = 12363298826181` |

## Por rodada

Cada rodada cola as suas faixas de 120 000 unidades. `N(b)` de uma faixa tem de ser igual ao `N(a)` da seguinte,
calculado por outro job, e cada zero isolado na reta tem de bater com a contagem (déficit 0).

| rodada | `de` | `até` | unidades | zeros na reta | déficit | execuções (GitHub Actions) |
|---|---|---|---|---|---|---|
| 0 (§13) | `3 000 175 332 800` | `3 000 175 342 471,5` | 9 671,5 | 41 393 | 0 | janela da seção 13 |
| 1 | `3 000 175 342 471,5` | `3 000 175 822 471,5` | 480 000 | 2 054 383 | 0 | 41559243734 |
| 2 | `3 000 175 822 471,5` | `3 000 181 222 471,5` | 5 400 000 | 23 111 813 | 0 | 41632268598, 41652868086, 41675244133, 41690164119, 41709096981 |
| 3 | `3 000 181 222 471,5` | `3 000 183 382 471,5` | 2 160 000 | 9 244 726 | 0 | 41749059161, 41777848348, 41809658688, 41809668823 |
| 4 | `3 000 183 382 471,5` | `3 000 184 822 471,5` | 1 440 000 | 6 163 151 | 0 | 41842620648, 41842633223 |
| 5 | `3 000 184 822 471,5` | `3 000 186 262 471,5` | 1 440 000 | 6 163 150 | 0 | 41889064559, 41889069781 |
| 6 | `3 000 186 262 471,5` | `3 000 187 702 471,5` | 1 440 000 | 6 163 152 | 0 | 41928307909, 41928311888 |
| 7 | `3 000 187 702 471,5` | `3 000 189 142 471,5` | 1 440 000 | 6 163 149 | 0 | 41993718376, 41993732554 |
| 8 | `3 000 189 142 471,5` | `3 000 190 582 471,5` | 1 440 000 | 6 163 152 | 0 | 42032164321, 42032176191 |
| 9 | `3 000 190 582 471,5` | `3 000 192 022 471,5` | 1 440 000 | 6 163 152 | 0 | 42080945931, 42080958292 |
| 10 | `3 000 192 022 471,5` | `3 000 193 462 471,5` | 1 440 000 | 6 163 151 | 0 | 42122478758, 42122490265 |
| 11 | `3 000 193 462 471,5` | `3 000 194 902 471,5` | 1 440 000 | 6 163 152 | 0 | 42698687986, 42698701000 |
| 12 | `3 000 194 902 471,5` | `3 000 196 342 471,5` | 1 440 000 | 6 163 151 | 0 | 42735880703, 42735893892 |
| 13 | `3 000 196 342 471,5` | `3 000 197 782 471,5` | 1 440 000 | 6 163 151 | 0 | 43020912910, 43020926543 |
| 14 | `3 000 197 782 471,5` | `3 000 199 222 471,5` | 1 440 000 | 6 163 153 | 0 | 43098888149, 43098890915 |
| 15 | `3 000 199 222 471,5` | `3 000 200 662 471,5` | 1 440 000 | 6 163 151 | 0 | 43131497894, 43131501697 |
| 16 | `3 000 200 662 471,5` | `3 000 202 102 471,5` | 1 440 000 | 6 163 152 | 0 | 43158851648, 43158854801 |
| 17 | `3 000 202 102 471,5` | `3 000 203 542 471,5` | 1 440 000 | 6 163 152 | 0 | 43188213296, 43188219425 |
| 18 | `3 000 203 542 471,5` | `3 000 204 982 471,5` | 1 440 000 | 6 163 152 | 0 | 43224609813, 43224615096 |
| 19 | `3 000 204 982 471,5` | `3 000 206 422 471,5` | 1 440 000 | 6 163 152 | 0 | 43267267316, 43267275902 |
| 20 | `3 000 206 422 471,5` | `3 000 207 862 471,5` | 1 440 000 | 6 163 152 | 0 | 43308900076, 43308905723 |
| 21 | `3 000 207 862 471,5` | `3 000 209 302 471,5` | 1 440 000 | 6 163 153 | 0 | 43344579894, 43344583905 |
| **total** | `3 000 175 332 800` | `3 000 209 302 471,5` | **33 969 671,5** | **145 389 043** | 0 | |

Conferências feitas ao gerar esta tabela a partir de `inicio.json`:

- as rodadas são contíguas;
- `12 363 153 437 138 + 41 393 = 12 363 153 478 531`, que é `N(3 000 175 342 471,5)`;
- `12 363 153 478 531 + 145 347 650 = 12 363 298 826 181`, que é `N(C0)`;
- `41 393 + 145 347 650 = 145 389 043`;
- `3 000 209 302 471,5 − 3 000 175 332 800 = 33 969 671,5`.

## Saídas parciais que não entram

Em 13/11/2026 às 09:30 UTC foram disparadas as execuções 43401822112 e 43401826709, para as faixas 0–11 a partir de
`3 000 209 302 471,5`. Elas foram canceladas às 09:46 UTC, quando a continuação foi pausada. Os arquivos que gravaram
estão em `resultados-continuacao`, em `de_3000209302471.5/` (commits `b2b44a0` e `780c2af`): faixas incompletas, sem
`zeros*.csv.gz`, com conclusão `inconclusivo`. **Não fazem parte dos valores fixados.**

## Retomada

A continuação só volta a rodar quando o autor pedir. O workflow `continuacao.yml` está desativado no GitHub Actions.
Para retomar, reative o workflow e dispare as faixas a partir do `C0` de `inicio.json`.
