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

Arquivos na ponta: 13; versões antigas em `historico/` (run-41554617926).

| commit | data (UTC) | execução | criados | mudados | apagados |
|---|---|---|---|---|---|
| `ae2573778` | 2026-11-03 06:11 | [41554617926](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41554617926) | `alturas.json`, `alturas.log`, `compila.log` | — | — |
| `97f5caab5` | 2026-11-03 11:34 | [41588835957](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41588835957) | `alturas_1e14.json`, `alturas_1e16.json`, `alturas_1e17.json`, `alturas_1e18.json`, `junta.log`, `resultados-log-14.txt` e mais 6 | `alturas.json` | `alturas.log`, `compila.log` |
| `94712505a` | 2026-11-03 11:49 | historico/: versões que execuções poster | — | — | — |

## `resultados-ataque`

Arquivos na ponta: 5.

| commit | data (UTC) | execução | criados | mudados | apagados |
|---|---|---|---|---|---|
| `6a385b635` | 2026-11-03 06:12 | [41588343004](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41588343004) | `QUEBRAS.md`, `RESUMO.md`, `ataque.json`, `ataque.log`, `quebras/faixa_3e12.json` | — | — |
| `16ec61219` | 2026-11-03 11:48 | [41593562501](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41593562501) | — | `RESUMO.md`, `ataque.json`, `ataque.log` | — |

## `resultados-continuacao`

Arquivos na ponta: 9.

| commit | data (UTC) | execução | criados | mudados | apagados |
|---|---|---|---|---|---|
| `5770e0b92` | 2026-11-03 04:47 | [41559243734](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41559243734) | `agrega.log`, `faixa0.json`, `faixa1.json`, `faixa2.json`, `faixa3.json`, `zeros0.csv.gz` e mais 3 | — | — |

## `resultados-fronteira`

Arquivos na ponta: 18; versões antigas em `historico/` (run-41557877448).

| commit | data (UTC) | execução | criados | mudados | apagados |
|---|---|---|---|---|---|
| `8dab5d232` | 2026-11-03 07:01 | [41557877448](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41557877448) | `RESUMO.md`, `fronteira.json`, `varreduras/varre_13_0.json`, `varreduras/varre_14_0.json`, `varreduras/varre_16_0.json`, `varreduras/varre_16_1000000000000.json` e mais 2 | — | — |
| `2bd792a5d` | 2026-11-03 11:45 | [41591657623](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41591657623) | `varreduras/varre_13_1000000000000.json`, `varreduras/varre_13_2000000000000.json`, `varreduras/varre_14_1000000000000.json`, `varreduras/varre_14_2000000000000.json`, `varreduras/varre_15_0.json`, `varreduras/varre_15_1000000000000.json` e mais 5 | `RESUMO.md`, `fronteira.json`, `varreduras/varre_13_0.json`, `varreduras/varre_14_0.json`, `varreduras/varre_16_0.json`, `varreduras/varre_16_1000000000000.json` e mais 1 | `varreduras/varre_18_1000000000000.json` |
| `bee424bff` | 2026-11-03 11:49 | historico/: versões que execuções poster | — | — | — |

## `resultados-nos`

Arquivos na ponta: 11.

| commit | data (UTC) | execução | criados | mudados | apagados |
|---|---|---|---|---|---|
| `eb7815737` | 2026-11-03 02:02 | [41560374464](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41560374464) | `NOS.md`, `atacados_faixa_3e12.json`, `atacados_faixa_3e12.log`, `nos_faixa_3e12.json`, `nos_faixa_3e12.log` | — | — |
| `f9c6e608e` | 2026-11-03 09:36 | [41580135724](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41580135724) | `atacados_continuacao_zeros0.json`, `atacados_continuacao_zeros1.json`, `atacados_continuacao_zeros1.log`, `nos_continuacao_zeros0.json`, `nos_continuacao_zeros0.log`, `nos_continuacao_zeros1.json` e mais 3 | `NOS.md` | `atacados_faixa_3e12.json`, `nos_faixa_3e12.json`, `nos_faixa_3e12.log` |
| `55e90b717` | 2026-11-03 11:16 | [41588342987](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41588342987) | — | `NOS.md`, `atacados_continuacao_zeros0.json`, `atacados_continuacao_zeros1.json`, `atacados_continuacao_zeros1.log` | — |

## `resultados-zeros`

Arquivos na ponta: 7; versões antigas em `historico/` (run-41542819161, run-41546782883).

| commit | data (UTC) | execução | criados | mudados | apagados |
|---|---|---|---|---|---|
| `66af61bad` | 2026-11-02 23:07 | [41542819161](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41542819161) | `baixo.json`, `compila.log`, `hardy_baixo.json`, `janelas.log`, `platt_baixo.json` | — | — |
| `004a0e11d` | 2026-11-02 23:53 | [41546782883](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41546782883) | `zeros.json`, `zeros_faixa.csv.gz` | `janelas.log` | — |
| `378c0401c` | 2026-11-03 00:09 | [41548734674](https://github.com/ShantiDraconis/clay-riemann-proof/actions/runs/41548734674) | — | `janelas.log`, `zeros.json`, `zeros_faixa.csv.gz` | — |
| `ca5e30bab` | 2026-11-03 11:50 | historico/: versões que execuções poster | — | — | — |

