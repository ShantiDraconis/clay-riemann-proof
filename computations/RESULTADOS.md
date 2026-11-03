# Onde estão os resultados dos cálculos

Cada workflow grava numa branch própria (`resultados-*`). Desde 2026-11-03 nenhuma execução apaga o que outra
gravou (`computations/grava_resultados.py`): arquivos com o mesmo nome são substituídos e o resto fica; cada branch
tem um `INDICE.md` com uma linha por execução. As versões anteriores estão no histórico do git e, para as que
execuções antigas tinham apagado ou substituído, também em `historico/run-<id>/`.

Para ler um arquivo sem trocar de branch:

    git fetch origin resultados-alturas
    git show origin/resultados-alturas:alturas.json
    git show COMMIT:varreduras/varre_18_0.json      # uma versão antiga, pelo commit da tabela

Gerado por `python3 computations/indice_resultados.py`.

## `resultados-alturas`

Arquivos na ponta: 22; versões antigas em `historico/` (run-41554617926).

| commit | data (UTC) | execução | criados | mudados | apagados |
|---|---|---|---|---|---|
| `ae2573778` | 2026-11-03 06:11 | [41554617926](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41554617926) | `alturas.json`, `alturas.log`, `compila.log` | — | — |
| `97f5caab5` | 2026-11-03 11:34 | [41588835957](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41588835957) | `alturas_1e14.json`, `alturas_1e16.json`, `alturas_1e17.json`, `alturas_1e18.json`, `junta.log`, `resultados-log-14.txt` e mais 6 | `alturas.json` | `alturas.log`, `compila.log` |
| `94712505a` | 2026-11-03 11:49 | historico/: versões que execuções poster | — | — | — |
| `caee02ae0` | 2026-11-03 16:32 | [41630806894](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41630806894) | `INDICE.md`, `log-zeros-18.txt`, `zeros_1e18.json`, `zeros_1e18_bruto.csv.gz` | — | — |
| `83e0bdf8f` | 2026-11-03 16:32 | [41630806894](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41630806894) | `contagem_1e18_b.json`, `log-contagem-18-b.txt` | `INDICE.md` | — |
| `a0cc9e631` | 2026-11-03 16:32 | [41630806894](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41630806894) | `contagem_1e18_a.json`, `log-contagem-18-a.txt` | `INDICE.md` | — |
| `9736b222c` | 2026-11-03 16:33 | [41630806894](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41630806894) | `alturas_1e18_tentativa.json` | `INDICE.md`, `alturas.json`, `junta.log` | — |

## `resultados-ataque`

Arquivos na ponta: 7; versões antigas em `historico/` (run-41588343004, run-41593562501, run-41594905434, run-41630112693).

| commit | data (UTC) | execução | criados | mudados | apagados |
|---|---|---|---|---|---|
| `6a385b635` | 2026-11-03 06:12 | [41588343004](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41588343004) | `QUEBRAS.md`, `RESUMO.md`, `ataque.json`, `ataque.log`, `quebras/faixa_3e12.json` | — | — |
| `16ec61219` | 2026-11-03 11:48 | [41593562501](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41593562501) | — | `RESUMO.md`, `ataque.json`, `ataque.log` | — |
| `2947c6c44` | 2026-11-03 12:14 | [41594905434](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41594905434) | — | `ataque.log` | `RESUMO.md`, `ataque.json` |
| `6a1921f11` | 2026-11-03 14:23 | [41630112693](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41630112693) | `ataque.json`, `quebras/zeros_1e14.json`, `quebras/zeros_1e16.json`, `quebras/zeros_1e17.json` | `QUEBRAS.md` | — |
| `5c9773b49` | 2026-11-03 14:23 | [41628698921](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41628698921) | — | `ataque.json` | — |
| `c3908b3e6` | 2026-11-03 15:22 | historico/: versões que execuções poster | — | — | — |

## `resultados-continuacao`

Arquivos na ponta: 21.

| commit | data (UTC) | execução | criados | mudados | apagados |
|---|---|---|---|---|---|
| `5770e0b92` | 2026-11-03 04:47 | [41559243734](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41559243734) | `agrega.log`, `faixa0.json`, `faixa1.json`, `faixa2.json`, `faixa3.json`, `zeros0.csv.gz` e mais 3 | — | — |
| `c97c439a4` | 2026-11-03 15:32 | [41632268598](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41632268598) | `INDICE.md`, `de_3000175822471.5/agrega.log`, `de_3000175822471.5/continuacao.json`, `de_3000175822471.5/faixa0.json`, `de_3000175822471.5/faixa1.json`, `de_3000175822471.5/faixa2.json` e mais 6 | — | — |

## `resultados-forca`

Arquivos na ponta: 8.

| commit | data (UTC) | execução | criados | mudados | apagados |
|---|---|---|---|---|---|
| `88d54fdf7` | 2026-11-03 14:55 | [41603222260](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41603222260) | `forca_1e14.json`, `forca_1e14.log`, `forca_1e16.json`, `forca_1e16.log`, `forca_1e18.json`, `forca_1e18.log` e mais 2 | — | — |

## `resultados-fronteira`

Arquivos na ponta: 18; versões antigas em `historico/` (run-41557877448).

| commit | data (UTC) | execução | criados | mudados | apagados |
|---|---|---|---|---|---|
| `8dab5d232` | 2026-11-03 07:01 | [41557877448](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41557877448) | `RESUMO.md`, `fronteira.json`, `varreduras/varre_13_0.json`, `varreduras/varre_14_0.json`, `varreduras/varre_16_0.json`, `varreduras/varre_16_1000000000000.json` e mais 2 | — | — |
| `2bd792a5d` | 2026-11-03 11:45 | [41591657623](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41591657623) | `varreduras/varre_13_1000000000000.json`, `varreduras/varre_13_2000000000000.json`, `varreduras/varre_14_1000000000000.json`, `varreduras/varre_14_2000000000000.json`, `varreduras/varre_15_0.json`, `varreduras/varre_15_1000000000000.json` e mais 5 | `RESUMO.md`, `fronteira.json`, `varreduras/varre_13_0.json`, `varreduras/varre_14_0.json`, `varreduras/varre_16_0.json`, `varreduras/varre_16_1000000000000.json` e mais 1 | `varreduras/varre_18_1000000000000.json` |
| `bee424bff` | 2026-11-03 11:49 | historico/: versões que execuções poster | — | — | — |

## `resultados-nos`

Arquivos na ponta: 9; versões antigas em `historico/` (run-41560374464, run-41580135724, run-41588342987, run-41628699123).

| commit | data (UTC) | execução | criados | mudados | apagados |
|---|---|---|---|---|---|
| `eb7815737` | 2026-11-03 02:02 | [41560374464](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41560374464) | `NOS.md`, `atacados_faixa_3e12.json`, `atacados_faixa_3e12.log`, `nos_faixa_3e12.json`, `nos_faixa_3e12.log` | — | — |
| `f9c6e608e` | 2026-11-03 09:36 | [41580135724](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41580135724) | `atacados_continuacao_zeros0.json`, `atacados_continuacao_zeros1.json`, `atacados_continuacao_zeros1.log`, `nos_continuacao_zeros0.json`, `nos_continuacao_zeros0.log`, `nos_continuacao_zeros1.json` e mais 3 | `NOS.md` | `atacados_faixa_3e12.json`, `nos_faixa_3e12.json`, `nos_faixa_3e12.log` |
| `55e90b717` | 2026-11-03 11:16 | [41588342987](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41588342987) | — | `NOS.md`, `atacados_continuacao_zeros0.json`, `atacados_continuacao_zeros1.json`, `atacados_continuacao_zeros1.log` | — |
| `0c46cd1fc` | 2026-11-03 16:32 | [41628699123](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41628699123) | `atacados_alturas_zeros_1e14.json`, `atacados_alturas_zeros_1e16.json`, `atacados_alturas_zeros_1e16.log`, `nos_alturas_zeros_1e14.json`, `nos_alturas_zeros_1e14.log`, `nos_alturas_zeros_1e16.json` e mais 1 | — | `NOS.md`, `atacados_continuacao_zeros0.json`, `atacados_continuacao_zeros1.json`, `atacados_continuacao_zeros1.log`, `nos_continuacao_zeros0.json`, `nos_continuacao_zeros0.log` e mais 4 |
| `1b6b087e3` | 2026-11-03 16:32 | [41665032655](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41665032655) | `INDICE.md` | `atacados_alturas_zeros_1e14.log` | — |
| `cd3c2f916` | 2026-11-03 17:37 | historico/: versões que execuções poster | — | — | — |

## `resultados-onda`

Arquivos na ponta: 19.

| commit | data (UTC) | execução | criados | mudados | apagados |
|---|---|---|---|---|---|
| `6d4662bf9` | 2026-11-03 12:14 | [41594905434](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41594905434) | `QUEBRAS.md`, `RESUMO.md`, `fronteira.json`, `varreduras/varre_14_10000000000000.json`, `varreduras/varre_14_11000000000000.json`, `varreduras/varre_14_12000000000000.json` e mais 13 | — | — |

## `resultados-zeros`

Arquivos na ponta: 7; versões antigas em `historico/` (run-41542819161, run-41546782883).

| commit | data (UTC) | execução | criados | mudados | apagados |
|---|---|---|---|---|---|
| `66af61bad` | 2026-11-02 23:07 | [41542819161](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41542819161) | `baixo.json`, `compila.log`, `hardy_baixo.json`, `janelas.log`, `platt_baixo.json` | — | — |
| `004a0e11d` | 2026-11-02 23:53 | [41546782883](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41546782883) | `zeros.json`, `zeros_faixa.csv.gz` | `janelas.log` | — |
| `378c0401c` | 2026-11-03 00:09 | [41548734674](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41548734674) | — | `janelas.log`, `zeros.json`, `zeros_faixa.csv.gz` | — |
| `ca5e30bab` | 2026-11-03 11:50 | historico/: versões que execuções poster | — | — | — |

