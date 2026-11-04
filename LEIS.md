# Leis, operadores e teoremas da análise dos zeros (seções 13 em diante)

**Autor:** Tiago Paschoalatto Fagliari (ShantiDraconis) — ORCID [0009-0006-6874-3910](https://orcid.org/0009-0006-6874-3910)
**Licença:** domínio público, [CC0 1.0 Universal](https://creativecommons.org/publicdomain/zero/1.0/legalcode)
(arquivo `LICENSE`). Pode copiar, modificar e usar para qualquer fim, sem pedir permissão. Citar
(`CITATION.cff`) é pedido, não obrigação.
**Estado:** `OPEN_MATH = true`. Nada aqui prova ou refuta a Hipótese de Riemann.

Este documento junta, num lugar só, o que saiu de todas as execuções desta análise. Cada item é de um destes tipos:
**teorema no kernel** (Lean 4 + Mathlib, `#print axioms` só com `propext`, `Classical.choice`, `Quot.sound`, fixado
em `ClayRiemannProof/Audit.lean`), **teorema com hipótese nomeada** (o kernel prova a implicação e o dado numérico
entra como hipótese), **teorema clássico** (da literatura, não formalizado aqui) ou **lei empírica** (medida nos
dados, não é teorema). Os itens marcados como candidatos a novos seguem a regra do projeto: só viram "novo" depois de
uma Proposta R1xx (enunciado + referência mostrando que não está na literatura) e do aceite do autor.

## 1. O objeto e os dados

- `ζ(½ + it) = e^{−iθ(t)} Z(t)`, `Z` real; `χ(s) = ζ(s)/ζ(1 − s)` e `χ(½ + it)^{1/2} = e^{−iθ(t)}`.
- **Lombada**: entre dois zeros vizinhos `γ₁ < γ₂`, `Z` tem um extremo de altura `|Z*|` em `t*`. Num par apertado,
  `Z ≈ a − c(t − m)²` com `a = |Z*|`, `c = |Z''|/2`.
- Dados certificados pela Arb (FLINT 3): 41 393 zeros em `3 000 175 332 800 < t ≤ 3 000 175 342 471,5` (seção 13);
  2 054 383 zeros contíguos até `3 000 175 822 471,5` (continuação) e mais 38 519 690 até `3 000 184 822 471,5` (segunda a nona extensões); 20 000 zeros em 10¹⁴, 10¹⁶ e 10¹⁷ (alturas);
  65 800 em 10¹⁸ (fronteira, 1ª onda). Todos na reta, contagens de Turing fechando.

## 2. Teoremas no kernel

| arquivo | teorema | enunciado |
|---|---|---|
| `Forca.lean` | `lombada_reais_iff` | os zeros de `(a − ε) − c(w − m)²` são todos reais ⟺ `ε ≤ a` |
| | `par_fora_da_reta` | para `ε > a`: zeros `m ± ib`, `b = √((ε − a)/c)`; em `s = ½ + iw`, `½ ∓ b + im` |
| | `lombada_do_par`, `limiar_do_par` | `c(w − γ₁)(γ₂ − w)` é a lombada de altura `c(γ₂ − γ₁)²/4 = |Z''|Δ²/8`; limiar `ε* = cΔ²/4` |
| | `calor_eh_empurrao` | no par isolado do fluxo de de Bruijn, `H_t = H_0 − 2t`: voltar o tempo `|t|` é empurrar `2|t|` |
| | `menos_forca` | o empurrão que tira da reta o par de uma lombada tira o de qualquer lombada mais baixa |
| | `empurrao_simetrico`, `constante_simetrica`, `zeta_empurrada_quarteto` | `ξ(½ + w) − ε·g(w)`, com `g` simétrico (`g(−w) = g(w)`, `g(w̄) = conj g(w)`; por exemplo `g = 1`), tem as duas simetrias de `ξ`, e seus zeros vêm em quartetos `w, −w, w̄, −w̄` |
| `Empurrao.lean` | `fora`, `fora_mono`, `fora_eq_zero_iff`, `limiar_da_janela`, `fora_total`, `fora_uniao`, `fora_composta`, `minimo_desce` | o operador de contagem `fora(s, h, ε) = 2·#{j : h_j < ε}`: monótono em `ε`; zero ⟺ `ε ≤ min h`; total acima de `max h`; aditivo em janelas disjuntas; `fora(h − ε, δ) = fora(h, ε + δ)` (semigrupo de translações); o mínimo só desce quando a janela cresce |
| | `empurrao_fixo_acaba_tirando` | se a lombada mais baixa das janelas tende a 0, todo empurrão fixo `ε > 0` acaba tirando zeros da reta |
| `Colisao.lean` | `colisao`, `raiz_quadrada`, `mais_proximo_sai_depois` | par isolado no fluxo do calor colide em `t = −Δ²/8` e sai da reta como `±i√(2(t* − t))` |
| `Lehmer.lean` | `csv_le_isolado`, `csv_ge`, `csv_neg` | cota de Csordas–Smith–Varga de um par de Lehmer: `−(5/32)Δ² ≤ λ ≤ −Δ²/8 < 0` |
| | `csv_limite` | sem vizinhos (`g → 0⁺`) a cota de CSV vira a lei da colisão `−Δ²/8` |
| | `csv_escala`, `csv_x_de_gamma` | em `x = c·γ`, `λ` vezes `c²`; de `γ` para `x = 2γ`, vezes 4 |
| `Paridade.lean` | `fora_par`, `furo_de_dois`, `contagem_fecha`, `fecha_de_contagens` | zeros fora da reta numa janela são em número par (`ρ` e `1 − ρ̄` na mesma altura); uma contagem de Turing que não fecha erra por pelo menos 2 |
| `Gram.lean` | `S_gram`, `zeros_no_bloco`, `bloco_par` | `S(g_m) = N(g_m) − m − 1 ∈ ℤ`; zeros no bloco = comprimento + variação de `S`; excesso e falta de 2 em 2 entre pontos bons |
| `QuartetoDesenhado.lean` | `quarteto_desenhado` | `ζ(0,3 ± 14i) ≠ 0` e `ζ(0,7 ± 14i) ≠ 0` (avaliação certificada de `ζ` no kernel, `|ζ| ≥ 1/10`) |
| `Turing.lean`, `PrimeiroFora.lean` | `turing_logica`, `primeiro_fora`, `primeiro_fora_acima` | lógica de Turing; se existe zero fora da reta, existe um de altura mínima, acima de toda altura verificada |
| `Parametro.lean` | `Q_na_reta_real`, `residuo_na_reta`, `residuo_minimo`, `residuo_cota`, `b_do_residuo` | o quarteto `½ ± b ± iγ₀` vale `(γ₀² − b² − t²)² + (2bγ₀)²` na reta: resíduo `m = (2bγ₀)²`, `≥ b⁴`, e `b = √m/(2γ₀)` |
| | `pontes_parametro`, `reta_ve_zero_iff` | `κ ≥ 0` ⟺ zeros do modelo na reta ⟺ a reta vê um zero ⟺ resíduo 0 ⟺ `−2κ ≤ 0` |
| | `tempo_de_colisao`, `par_na_reta_kappa`, `quarteto_satura_de_bruijn` | no fluxo `κ(t) = κ + t/2`: na reta exatamente para `t ≥ −2κ`; par na reta `−Δγ²/2`, quarteto fora `2b² = Δ²/2` (cota de de Bruijn com igualdade) |
| | `lambda_le_dois_b2`, `de_bruijn_meio`, `sem_residuo_lambda_le_zero`, `target_lambda_zero`, `residuo_de_lambda` | com `DeBruijnFaixa` e `H0_eh_xi` (nomeados): `Λ ≤ 2·b_sup²`, `Λ ≤ ½`, meta ⟹ `Λ = 0` (com Rodgers–Tao), `Λ > 0` ⟹ zero com `|Re ρ − ½| > b` se `2b² < Λ` |
| | `lombada_minimo`, `b_da_lombada`, `S_reta_cai_dois` | `b = √(2|Z_min|/|Z''|)`; `S_reta = S − 2k` |
| | `media_absorvida`, `media_do_espelho`, `eixo_unico`, `espelho_conta` | a média de `½ + b(s − 1)` é ½ para quaisquer gaps; `(Re ρ + Re(1 − ρ̄))/2 = ½` para todo `ρ`; ½ é o único eixo de `s ↦ 1 − s̄`; conjunto simétrico tem tantos `s < x` quanto `s > 2 − x` |
| | `euler_meio_diverge`, `meio_nao_eh_inv_raiz`, `triviais_fora_de_xi` | `Σ p^{−1/2}` diverge; `1/√p ≠ ½`; `ξ(−2(n + 1)) ≠ 0` |
| `Geometrias.lean` | `circulo_iff`, `circulo_eh_reta` | raízes de `1 − λu + qu²` no círculo `|u|² = 1/q` ⟺ `λ² ≤ 4q`; `|q^{−s}|² = 1/q` ⟺ `Re s = ½` |
| | `hasse_F5`, `hasse_F7`, `hasse_F11`, `hasse_F13`, `hasse_justo`, `rh_curva`, `rh_curva_reta`, `rh_todas_F13` | toda curva `y² = x³ + ax + b` sobre `𝔽₅ … 𝔽₁₃` tem `a_p² ≤ 4p` (contagem no kernel): RH da curva |
| | `petersen_ramanujan`, `prisma_nao_ramanujan`, `prisma_zeros_fora` | Petersen é Ramanujan (RH de Ihara); `K₇ □ K₂` não é: zeros `s = log 2/log 6`, `log 3/log 6` fora da reta |
| | `selberg_reta`, `desvio_de_lambda`, `selberg_316`, `kim_sarnak` | `s(1 − s) = λ` na reta ⟺ `λ ≥ ¼`; desvio `≤ ¼` com `3/16`, `≤ 7/64` com `975/4096` |
| `Identidades.lean` | `defeito_circulo`, `defeito_espelho`, `target_iff_defeito_zero`, `nao_target_iff` | `1 − |1 − 1/ρ|² = (2 Re ρ − 1)/|ρ|²`: RH ⟺ defeito 0 em todo zero; refutação ⟺ zero com `Re ρ < ½`, com `|1 − 1/ρ|² = 1 + 2b/|ρ|²` |
| | `li_aparece`, `li_aparece_para_zero` | `|w|² ≥ 1 + δ` ⟹ `|wⁿ| ≥ 2` para `n ≥ 3/δ`; um zero fora aparece no critério de Li em `n ≈ 1,5γ²/b` |
| | `defeito_tende_a_zero`, `defeito_some_na_altura`, `familia_simetrica`, `colisao_no_circulo` | defeito `2b/|ρ|² → 0` com `b → 0`, `≤ 2b/γ²`; `A + tB` simétrica; transição = zero duplo |
| | `robin_refuta`, `lagarias_refuta`, `vonKoch_refuta`, `mertens_refuta`, `lambda_positivo_refuta` | com os enunciados nomeados: um `n` refuta (Robin, Lagarias); `ψ` e `M` pedem violações sem cota; `Λ > 0` refuta |
| `Maquina.lean` | `harm_eq_sum`, `lag_iff`, `maquina_iff`, `rh_iff_maquina_nunca_para`, `refutacao_finita`, `rh_pi1` | com `LagariasPi1` (nomeado): RH ⟺ a máquina que testa `(H_{δ(n)} − n²/2)² < 36n³` nunca para; refutar = ela parar num `N` finito; RH é Π₁ |
| | `lag_ate_6`, `maquina_6`, `delta_valores` | o kernel rodou a máquina até `n = 6` (`δ(6) = 8 640`): não parou |
| | `Q_kappa_zero` | o terceiro estado `κ = 0`: `Q = (w − iγ₀)²(w + iγ₀)²`, zero duplo na reta |
| | `positividade_iff`, `ponte_hodge`, `positividade_iff_hasse`, `positividade_F13` | `m² − λmn + qn² ≥ 0` ∀ `m, n` ⟺ `λ² ≤ 4q` ⟺ RH do fator (a ponte de Weil/Hodge); todas as curvas sobre `𝔽₁₃` |
| | `hasse_E0_97`, `hasse_E1_97`, `E0_supersingular_97` | RH local dos fatores de `L(E, s)` para `y² = x³ − x` e `y² = x³ − 2`, `5 ≤ p ≤ 97`; `a_p = 0` para `p ≡ 3 (mod 4)` |
| `Nos.lean` | `no_discriminante`, `frobenius_iff_circulo`, `reta_iff_circulo`, `todo_u_eh_potencia` | TFAE: `λ² ≤ 4q` ⟺ positividade ⟺ círculo `|u|² = 1/q` ⟺ Frobenius `|α|² = q` ⟺ reta `Re s = ½` (`q > 1`) |
| | `equacao_funcional_local`, `simetria_eh_conjugacao` | `P(1/(qu)) = P(u)/(qu²)`; `|u|² = 1/q ⟺ ū = 1/(qu)` (o parceiro funcional é o conjugado) |
| | `quartica_fatora`, `quartica_par_fora`, `saturacao_superior`, `saturacao_inferior` | lombada quártica: o par fora com `b²` exato e a saturação da lei da raiz quadrada (L5) |
| | `calor4_t`, `calor4_x`, `calor4_xx`, `calor4_equacao`, `calor4_inicio`, `calor4_centro` | calor exato na lombada quártica e o empurrão efetivo (L6) |
| `Fracoes.lean` | `gauss_kuzmin_produto`, `gauss_kuzmin_soma`, `gauss_kuzmin_menor_que_um` | `Σ_{k≤n} log₂(1 + 1/(k(k+2))) = log₂(2(n+1)/(n+2)) < 1`: a lei das caudas em frações |
| | `chi_euclidianos`, `chi_esferico_235`, `beal_chi`, `beal_folga`, `hiperbolico_maximo` | `χ = 1/x + 1/y + 1/z`: euclidianos `= 1`; maior `χ < 1` é `41/42`; Beal `≤ 1`, `≤ 11/12` fora de `(3,3,3)` |
| | `fermat_generalizado_gigantes`, `chi_das_gigantes`, `beal_com_fator`, `beal_mundo_6`, `beal_cota_C`, `beal_ate_6` | as 10 soluções primitivas conhecidas com `χ < 1`; Beal sem contraexemplo nas bases `≤ 6`, expoentes 3–5 |
| | `serrin_criticos`, `energia_supercritica`, `kolmogorov` | `2/p + 3/q`: críticos `= 1`, energia `3/2`; o expoente de Kolmogorov `−5/3` por análise dimensional |
| | `liberdade_assintotica_iff`, `qcd_beta0`, `qcd_quebra` | `β₀ > 0 ⟺ n_f < 11N/2`; QCD `β₀ = 7`; quebra em `n_f = 33/2` |
| | `primeiro_momento_3sat`, `primeiro_momento_justo` | primeiro momento do 3-SAT: o limiar `ln 2/ln(8/7)` está entre `5,18` e `5,2` (inteiros de 234 dígitos) |
| | `E0_ordinario_97`, `E0_metade_97`, `defeito_no_alto`, `li_indice_no_alto` | `y² = x³ − x`: `a_p = 0 ⟺ p ≡ 3 (mod 4)` até 97 (12 de 23); números minúsculos e gigantes da RH |
| `CertificateBridge.lean` | `window_on_line_from_certificates`, `zeroFreeRect_of_peca_ret`, `injOn_of_second_derivative_bound` | bolas injetivas + retângulos sem zeros + cobertura ⟹ zeros da janela na reta (trazido da branch, README §46) |
| `CertifiedZeros/FirstZero.lean`, `HeightThirteen.lean` | `cert_ok`, `zero_na_linha`, `primeiro_zero`, `zero_simples`, `Z_nao_vazio`, `altura_do_primeiro_zero` | o primeiro zero certificado pelo kernel: `ζ(½ + iγ) = 0` com `|γ − 14,1347251417| ≤ 10⁻⁶`, `Re ρ₁ = ½` exato (contração + simetria), único na bola e simples; com a faixa até 13, o zero mais baixo tem altura em `(13; 14,1347261417]` |

## 3. Teoremas com hipótese nomeada (dados da Arb)

| teorema | hipótese | conclusão |
|---|---|---|
| `Continuacao.rhAteZ_continuacao` | Platt–Trudgian 2021 + `JanelaArb2026` + `JanelaContinuacao2026` | RH até 3 000 175 822 471 |
| `Continuacao.primeiro_fora_acima_continuacao` | as mesmas | o primeiro zero fora da reta, se existir, tem `Im > 3 000 175 822 471` |
| `Continuacao.rhAteZ_continuacao2` | Platt–Trudgian 2021 + `JanelaArb2026` + `JanelaContinuacao2026` + `JanelaContinuacao2026b` (16 faixas, 8 217 533 zeros) | RH até 3 000 177 742 471 |
| `Continuacao.primeiro_fora_acima_continuacao2` | as mesmas | o primeiro zero fora da reta, se existir, tem `Im > 3 000 177 742 471` |
| `Continuacao.par_mais_fragil_continuacao2` | bolas do par 12 363 161 233 435/436 (`s = 0,0031`) | `−3,35·10⁻⁷ ≤ λ ≤ −2,67·10⁻⁷` |
| `Continuacao.rhAteZ_continuacao3` | as anteriores + `JanelaContinuacao2026c` (faixas 16–35; 36 faixas, 18 489 450 zeros desde 3 000 175 822 471,5) | RH até 3 000 180 142 471 |
| `Continuacao.primeiro_fora_acima_continuacao3` | as mesmas | o primeiro zero fora da reta, se existir, tem `Im > 3 000 180 142 471` |
| `Continuacao.par_mais_fragil_continuacao3` | bolas do par 12 363 167 808 945/946 (`s = 0,0026`) | `−2,40·10⁻⁷ ≤ λ ≤ −1,91·10⁻⁷` (o par mais perto da colisão até a sétima extensão) |
| `Continuacao.rhAteZ_continuacao4` | as anteriores + `JanelaContinuacao2026d` (faixas 36–44; 45 faixas, 23 111 813 zeros desde 3 000 175 822 471,5) | RH até 3 000 181 222 471 |
| `Continuacao.primeiro_fora_acima_continuacao4` | as mesmas | o primeiro zero fora da reta, se existir, tem `Im > 3 000 181 222 471` |
| `Continuacao.par_mais_fragil_continuacao4` | bolas do par 12 363 175 635 090/091 (`s = 0,0071`) | `−1,74·10⁻⁶ ≤ λ ≤ −1,39·10⁻⁶` |
| `Continuacao.rhAteZ_continuacao5` | as anteriores + `JanelaContinuacao2026e` (faixas 0–5 do C0 3 000 181 222 471,5; 3 081 576 zeros) | RH até 3 000 181 942 471 |
| `Continuacao.primeiro_fora_acima_continuacao5` | as mesmas | o primeiro zero fora da reta, se existir, tem `Im > 3 000 181 942 471` |
| `Continuacao.par_mais_fragil_continuacao5` | bolas do par 12 363 179 255 965/966 (`s = 0,0078`) | `−2,10·10⁻⁶ ≤ λ ≤ −1,67·10⁻⁶` |
| `Continuacao.rhAteZ_continuacao6` | as anteriores + `JanelaContinuacao2026f` (faixas 6–11 do C0 3 000 181 222 471,5; 3 081 575 zeros) | RH até 3 000 182 662 471 |
| `Continuacao.primeiro_fora_acima_continuacao6` | as mesmas | o primeiro zero fora da reta, se existir, tem `Im > 3 000 182 662 471` |
| `Continuacao.par_mais_fragil_continuacao6` | bolas do par 12 363 184 245 937/938 (`s = 0,0070`) | `−1,67·10⁻⁶ ≤ λ ≤ −1,32·10⁻⁶` |
| `Continuacao.rhAteZ_continuacao7` | as anteriores + `JanelaContinuacao2026g` (faixas 12–17; 3 081 575 zeros) | RH até 3 000 183 382 471 |
| `Continuacao.primeiro_fora_acima_continuacao7` | as mesmas | o primeiro zero fora da reta, se existir, tem `Im > 3 000 183 382 471` |
| `Continuacao.par_mais_fragil_continuacao7` | bolas do par 12 363 185 811 880/881 (`s = 0,0050`) | `−8,61·10⁻⁷ ≤ λ ≤ −6,88·10⁻⁷` |
| `Continuacao.rhAteZ_continuacao8` | as anteriores + `JanelaContinuacao2026h` (faixas 0–5 do C0 3 000 183 382 471,5; 3 081 575 zeros) | RH até 3 000 184 102 471 |
| `Continuacao.primeiro_fora_acima_continuacao8` | as mesmas | o primeiro zero fora da reta, se existir, tem `Im > 3 000 184 102 471` |
| `Continuacao.par_mais_fragil_continuacao8` | bolas do par 12 363 187 982 787/788 (`s = 0,0016`) | `−8,30·10⁻⁸ ≤ λ ≤ −6,63·10⁻⁸` (o par mais perto da colisão em todos os dados) |
| `Continuacao.rhAteZ_continuacao9` | as anteriores + `JanelaContinuacao2026i` (faixas 6–11; 3 081 576 zeros) | RH até 3 000 184 822 471 |
| `Continuacao.primeiro_fora_acima_continuacao9` | as mesmas | o primeiro zero fora da reta, se existir, tem `Im > 3 000 184 822 471` |
| `Continuacao.par_mais_fragil_continuacao9` | bolas do par 12 363 193 959 653/654 (`s = 0,0075`) | `−1,91·10⁻⁶ ≤ λ ≤ −1,52·10⁻⁶` |
| `Continuacao.par_mais_fragil_continuacao` | bolas da Arb do par 12 363 153 756 750/751 e `Δ²g ≤ 4/5` | `−5,75·10⁻⁷ ≤ λ ≤ −4,59·10⁻⁷` |
| `Continuacao.par_mais_fragil_1e18` | bolas do par 6 144 758 226 908 699 989/990 | `−1,013·10⁻⁵ ≤ λ ≤ −8,09·10⁻⁶` |
| `Continuacao.par_mais_fragil_onda2` | bolas do par 467 888 702 979 044/045 (2ª onda da fronteira, 7 791 406 zeros) | `−6,93·10⁻⁷ ≤ λ ≤ −5,53·10⁻⁷` |
| `Continuacao.par_mais_fragil_onda_1e14` | bolas do par 472 888 703 009 302/303 (onda em 10¹⁴, 8 661 651 zeros) | `−9,20·10⁻⁷ ≤ λ ≤ −7,35·10⁻⁷` |
| `Alturas.par_mais_fragil_1e14` | bolas do par 467 888 702 924 344/345 (janela certificada de 10¹⁴) | `−2,79·10⁻⁵ ≤ λ ≤ −2,23·10⁻⁵` |
| `Alturas.par_mais_fragil_1e16` | bolas do par 54 118 226 280 296 885/886 (janela de 10¹⁶, `s = 0,0078`) | `−1,22·10⁻⁶ ≤ λ ≤ −9,72·10⁻⁷` |
| `Alturas.par_mais_fragil_1e17` | bolas do par 577 829 042 746 908 883/884 (janela de 10¹⁷) | `−2,86·10⁻⁵ ≤ λ ≤ −2,28·10⁻⁵` |
| `Lehmer.aglomerado_052_053`, `Lehmer.par_mais_fragil` | bolas da seção 13 | `λ ∈ [−6,23·10⁻⁴, −4,98·10⁻⁴]`, `[−3,99·10⁻⁵, −3,18·10⁻⁵]` |
| `Gram.aglomerado_rosser` | `N` nos três pontos de Gram | a exceção de Rosser do aglomerado (blocos 3/1 e 0/2) |
| `Paridade.no_aglomerado_sem_fora` | `N(T_b) − N(T_a) = 11` e 11 zeros na reta | nenhum zero fora da reta no nó do aglomerado |

## 4. Teoremas clássicos ligados aos dados (e o teste que os dados permitem)

| teorema | o que diz | teste nos dados |
|---|---|---|
| Conrey–Ghosh (1985) e Hughes–Lugmayer–Pearce-Crump (2024), sob RH | `Σ_{γ ≤ T} max_{[γ,γ⁺]} |ζ|² = (e² − 5)/2·(T/2π)L² + α₋₁(T/2π)L + O(T)`, `L = log(T/2π)`, `α₋₁ = 5 − e² − 10γ₀ + 2e²γ₀ ≈ 0,369`; por lombada, na altura `T`: `aL + 2a + α₋₁ + O(1/L)` | **média de `Z*²` nas 41 392 lombadas da seção 13: 34,91 ± 1,13. Previsto: 34,90 com os termos de ordem menor; 32,12 só com o termo principal** |
| Hardy–Littlewood | `∫₀^T Z² dt ~ T log(T/2π)`: média quadrática de `Z` ≈ `√log(T/2π)` | 5,19 em 3·10¹²; a média quadrática nas lombadas é 5,91 (os extremos ficam acima da média, como Conrey–Ghosh prevê) |
| Selberg (TCL) | `log|ζ(½ + it)| / √(½ log log T)` tende à normal | nas lombadas, `log|Z*|`: média 0,31, variância 1,80 contra `½ log log(T/2π) = 1,65`, assimetria −0,33 |
| Montgomery, GUE | espaçamentos com repulsão `p(s) ~ (π²/3)s²` | 41 392 espaçamentos normalizados da seção 13: variância 0,1756 (Wigner para o GUE: `3π/8 − 1 = 0,1781`) |
| Rodgers–Tao (2018) | `Λ ≥ 0` | as cotas de Lehmer `Λ ≥ λ_CSV` (seção 3) ficam abaixo de 0: hoje são estatística do fenômeno de Lehmer, não cotas novas para `Λ` |
| Polymath 15 (2019) | `Λ ≤ 0,22` | não testável com estes dados |
| Csordas–Smith–Varga (1994) | `Λ > λ_k` para todo par de Lehmer | hipótese, não formalizado; a cota em si está no kernel (seção 2) |
| Davenport–Heilbronn | combinação de funções L com equação funcional e sem produto de Euler tem zeros fora da reta | é o que `ζ_ε = ζ − ε·χ^{1/2}` faz (seção 6) |
| Lehman (1970) | primeira violação da regra de Rosser perto do zero 13 999 525 | uma violação na seção 13 (o aglomerado), frequência compatível |
| Platt–Trudgian (2021) | RH até 3 000 175 332 800 | hipótese nomeada `PlattTrudgian2021` |

## 5. Leis empíricas medidas

1. **Escala do par mais frágil**: `λ_min ≈ −½(9/(π²N))^{2/3}/ρ²`. Seção 13: −3,19·10⁻⁵ (previsto −2,1·10⁻⁵);
   continuação: −4,59·10⁻⁷ (previsto −1,6·10⁻⁶); 10¹⁸: −8,10·10⁻⁶ (previsto −1,05·10⁻⁵); 10¹⁴: −2,23·10⁻⁵
   (−2,73·10⁻⁵); 10¹⁶: −9,73·10⁻⁷ (−2,06·10⁻⁵). O que decide é o número de zeros, não a altura.
2. **A lombada do par**: `log|Z*| = 2,02·log Δ + c` nos 1 119 pares com `s < 0,3`: a altura cresce com o quadrado da
   distância (`|Z*| = |Z''|Δ²/8`, `Forca.limiar_do_par`).
3. **Cauda baixa das alturas**: `F(ε) = P(|Z*| < ε) ∝ ε^{1,32}` em `[0,01; 0,32]`; o GUE com `|Z*| ∝ Δ²` prevê o
   expoente `3/2` no limite `ε → 0`.
4. **A lombada mais baixa desce com a janela**: 1,034·10⁻³ em 41 393 zeros, 5,34·10⁻⁵ em 2 095 776: expoente 0,755
   (o GUE prevê 2/3). Junto com `Empurrao.empurrao_fixo_acaba_tirando`, é o que sustenta "todo empurrão fixo acaba
   tirando zeros da reta".
5. **Fração tirada da reta** (`Z ∓ ε`, seção 13): 0 até `ε = 10⁻³`; 3,4% em 0,1; 39% em 1 (0,19 da média
   quadrática); 86% em 5,6 (1,1 da média quadrática); 99,4% em 31,6; todos em 129,5. Os dois sentidos do empurrão dão a
   mesma curva. Gráfico: `computations/forca/resultados/fracao_fora.png`.
6. **Saturação depois do limiar**: até `b ≈ 0,05` vale `ε = |Z*| + b²|Z''|/2`; depois o par se afasta mais devagar.
   Para `b = 0,2` (o quarteto visível): par plano 976 477 (`Z'' = −23`) pede `ε = 2,56` (0,49 da média quadrática);
   par 570 515 pede 4,63 (modelo: 2,0); par íngreme 756 750 (`Z'' = +1 069`) não chega com `ε ≤ 30`.
7. **Empurrão e calor ordenam os pares de modos diferentes**: o calor (`Δ_x²/8`) favorece o par mais apertado; o
   empurrão (`|Z''|Δ²/8`) favorece o par onde `Z` é plano. O ponto mais fácil por empurrão em 3·10¹² é o par
   12 363 153 570 515 (`|Z*| = 5,3·10⁻⁵`); por calor, o par 12 363 153 756 750 (`4,6·10⁻⁷`).
8. **`S(t)` extremo não é fragilidade**: os nós só com `S` extremo pedem 0,07 a 0,45; os nós com par frágil, 10⁻³.
9. **Ponto mais rígido da seção 13**: o maior vazio (zeros 448 671/672, `s = 2,81`), lombada de 129,5 = 25 vezes a
   média quadrática.
10. **O produto de Euler prevê as lombadas** (seção 35): `log|P_X(t*)|` com `X = 10⁴` no extremo da lombada tem
    correlação 0,89 com `log|Z*|` nas 41 392 lombadas de `3·10¹²`. No 1% com o menor `P_X`, 58% das lombadas ficam
    abaixo de 0,1, contra 3,4% no total. Para os pares mais apertados a correlação é menor (0,40 a 0,49 com `log s` em
    `10¹⁴`, `10¹⁶`, `10¹⁷`): o produto enxerga o empurrão, não o calor.
11. **O CUE de tamanho `N = log(T/2π)` reproduz a distribuição das lombadas** (seção 35): com `N = 27`, a fração
    abaixo de cada `ε` bate com a medida em `3·10¹²` a menos de um ponto (39,2% contra 39% em `ε = 1`; 85,7% contra 86%
    em `ε = 5,6`; mediana 1,455 contra 1,43). Na cauda, a lombada mínima prevista é cerca de 2 vezes menor que a medida.

12. **A largura das lombadas cresce como `½ log log T`** (seção 28): var `log|Z*|` = 1,804 ± 0,014 em `3·10¹²` e
    1,896 ± 0,063 em `10¹⁴` (aumento previsto 0,061). No CUE, `var = 0,516·log N + 0,21` de `N = 27` a `2 301`, com a
    mediana parada em ≈ 1,4: um empurrão fixo tira uma fração que tende a ½, e um empurrão do tamanho da média
    quadrática tira todos os pares, menos uma fração que vai a 0 (`10^(−2,67·10^7000000)` na torre
    `10^(10^(11·10^7000000))`; extrapolação condicional).

**Lei-modelo (extrapolação pelo CUE, seção 35)**: a lombada mediana fica em ≈ 1,4 em qualquer altura; a variância de
`log` lombada cresce (1,9 em `3·10¹²`, 4,2 em `10¹⁰⁰⁰`); a fração tirada da reta por um empurrão do tamanho da média
quadrática vai de 85% a 96%; a lombada mínima em 10⁴ zeros cai de 1,4·10⁻³ para 2,1·10⁻⁴, e o `λ` do par mais
apertado, de −5,5·10⁻⁵ para −7,6·10⁻⁹. Isso é modelo, não medida: nessas alturas ninguém calcula `ζ`.

## 6. Operadores, operações e conjuntos

- **Empurrão** `P_ε : Z ↦ Z − ε` na reta; no plano `ζ_ε = ζ − ε·χ^{1/2}`; na forma completada `ξ ↦ ξ − ε·g`, `g`
  simétrico. Preserva a equação funcional e a conjugação, quebra o produto de Euler. Os empurrões formam o semigrupo
  `(ℝ≥0, +)` (`Empurrao.fora_composta`).
- **Conjunto das alturas** `H(W) = {|Z*_j|}` de uma janela `W`, separado em positivas e negativas (o sinal alterna de
  uma lombada para a outra).
- **Contagem** `fora(W, ε) = 2·#{h ∈ H(W) : h < ε}`; **limiar da janela** `E(W) = min H(W)` (`limiar_da_janela`),
  antítono em `W` (`minimo_desce`).
- **Fluxo do calor** `H_t`: para o par, `H_t = H_0 − 2t` (`calor_eh_empurrao`): o tempo é um empurrão.
- **Cota de CSV** `(Δ, g) ↦ λ`, com `−(5/32)Δ² ≤ λ ≤ −Δ²/8` e escala `c²`.
- **Torção** `s ↦ 1 − s̄`: involução sem pontos fixos nos zeros fora da reta, daí a paridade da contagem.
- **Reticulado de Gram**: `S(g_m) ∈ ℤ`, blocos entre pontos bons com excesso e falta pares.

## 7. Linhas de pesquisa (as lacunas)

| linha | classe | o que falta |
|---|---|---|
| L1. A lombada mais baixa `E(T)` tende a 0? | consequência condicional (candidata) | os pequenos espaçamentos não bastam sozinhos: é preciso controlar `|Z''|` no par. Sob o GUE, `E(T) ~ N(T)^{−2/3}` (lei 4 mede 0,755). Com `E(T) → 0`, `empurrao_fixo_acaba_tirando` dá a conclusão no kernel |
| L2. A constante de empurrão `E_∞ = inf_T E(T)` e a família `ξ − εg` | candidata a novo (Proposta R1xx, aguardando decisão) | análogo por empurrão de `Λ ≥ 0` (Rodgers–Tao): conjectura `E_∞ = 0`, ou seja, `ζ` está na borda também para empurrões. Conferir se o método de Rodgers–Tao (fluxo + correlação de pares) se adapta |
| L3. A distribuição das alturas das lombadas (espectro de rigidez) | candidata a novo (Proposta R1xx) | cauda `ε^{3/2}`, média de Conrey–Ghosh, corpo próximo do log-normal de Selberg; comparar com os extremos do polinômio característico do CUE (literatura a conferir) |
| L4. Forças certificadas em todas as lombadas | ferramenta | `forca.yml` (Arb) nos pares escolhidos já está na fila; `lombadas.py` em todos os 2,1 milhões leva umas 21 h em 2 núcleos (cabe numa matriz do CI) |
| L5. A lei de saturação além do quadrático | **fechada no modelo** (`Nos.lean`) | `quartica_par_fora`: `b² = (√(c² + 4d(ε − A)) − c)/(2d)`; `saturacao_superior`/`saturacao_inferior`: `(ε − A)/c − d(ε − A)²/c³ ≤ b² ≤ (ε − A)/c`; nos zeros de DH e Epstein o termo quártico leva 10 de 13 pares a erro ≤ 2 % (README §44) |
| L6. Empurrão ⟷ calor fora do par isolado | **fechada no modelo** (`Nos.lean`) | `calor4`: `H_t = f − t f'' + (t²/2) f''''` é solução exata de `∂ₜH = −∂²ₓH` na lombada quártica; `calor4_centro`: o empurrão efetivo é `|t||f''(0)| − (t²/2) f''''(0)` |
| L7. Os pares de Lehmer depois de Rodgers–Tao | reformulação | as cotas `Λ ≥ λ` já são superadas por `Λ ≥ 0`; o valor dos pares frágeis está na estatística (L3) |
| L8. `Z − ε` exatamente, no kernel | ferramenta | o `g` que corresponde a `Z − ε` é `(π^{−1/2}Γ(s/2)Γ((1 − s)/2))^{1/2}` (simétrico, mas o ramo da raiz tem de ser fixado na faixa); hoje o kernel tem o caso geral com `g` simétrico e a instância `g = 1` |

## 8. Correções a resumos que circularam

- Os nomes `g_symm`, `g_conj`, `xi_eps_symm`, `xi_eps_conj`, `limiar_exato`, `b_sqrt`, `modelo_par_unico` e
  `ponte_calor` não existem no repositório; os nomes certos estão na seção 2.
- O limiar provado é o do **modelo** da lombada (quadrático), exato para o modelo. Para uma `Z` qualquer, "dois zeros
  na reta ⟺ `ε ≤ |Z*|`" vale numa lombada de um só pico (valor intermediário); que os dois zeros passem a ser um par
  complexo pede a contagem de zeros da função analítica, não só Bolzano, e não está formalizado.
- As forças `5,3·10⁻⁵`, `1,05·10⁻⁴`, … e as dos nós são **estimativas** por Riemann–Siegel (conferidas: `|Z|` nos
  próprios zeros ≤ 10⁻⁸). Não são teoremas no kernel. As versões certificadas (bolas da Arb) vêm do workflow
  `forca.yml`. A contagem "17 teoremas fechados" misturava teoremas e estimativas.
- `Λ ≥ −4,59·10⁻⁷` (de CSV) é verdadeira, mas mais fraca que `Λ ≥ 0`, já provado por Rodgers–Tao.
- Os zeros em 3·10¹² e 10¹⁸ já são certificados (bolas da Arb); o que ainda espera a Arb são os **valores de força**.
- "Absorver o ½ nas caudas" (`Re = ½ + b(s − 1)` ou `s/2`) não é lei: a média ½ vem da normalização de `s`
  (`Absorcao.media_reAbs`, `media_absorvida`) e vale para qualquer configuração, com zeros fora ou não
  (`media_do_espelho`). O número absorvido
  quebra a simetria `s ↦ 1 − s̄` (no bloco, 23 gaps com `s < 1/100` contra 247 382 com `s > 199/100`).
- O "fator 4 pelos vizinhos" entre `−d²/8` e `−d²/2` é a coordenada `z = 2γ` (`recorde_lambda_exato`); os vizinhos
  mudam a cota de CSV em no máximo 25 %. A média dos gaps é `(γ_último − γ_primeiro)/(N − 1)` (`recorde_media`), não
  `L/N` nem `L/(N − 1)`. `b(t)` é raiz de racional: `b(−10⁻⁶) = 0,000 635 9…`, não `3/5 000`.
- O erro da bola no gap recorde é `8,5·10⁻¹⁵` do gap (`bola_relativa`), não 1,6 %. `s < 1/300` são 2 pares, não 1.
- Epstein `m² + 5n²` até `Im 100` tem 13 zeros fora da reta (o 13º, `0,81117 + 58,50774i`, achado pela contagem na
  reta; README §39), não 12.

## 9. Como reproduzir

Scripts em `computations/` (zeros, alturas, fronteira, ataque, quebras, nós, continuação, força), workflows em
`.github/workflows/`, resultados nas branches `resultados-*` e em `computations/*/resultados/`. Lean:
`lake build` (o `Audit.lean` confere os axiomas de cada declaração).
