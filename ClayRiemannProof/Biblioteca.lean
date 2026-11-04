import ClayRiemannProof.Biblioteca.HilbertPolya
import ClayRiemannProof.Biblioteca.Euler
import ClayRiemannProof.Biblioteca.Entradas
import ClayRiemannProof.Biblioteca.Reducao

/-!
# Biblioteca RH: o que um ataque à Hipótese de Riemann precisa ter à mão no Lean

Organizada como o Mathlib, um arquivo por área. O alvo é sempre o `RiemannHypothesis` do Mathlib.

* `Biblioteca/HilbertPolya.lean` — o operador de Hilbert–Pólya como estrutura (`OperadorHilbertPolya`), a entrada
  aberta `HilbertPolya` e a ponte provada `rh_de_hilbertPolya` (autovalor de operador simétrico é real).
* `Biblioteca/Euler.lean` — o produto de Euler (`Re s > 1`), a ausência de zeros em `Re s ≥ 1` e as três fronteiras
  das somas sobre primos (`σ > 1`, `σ > ½`, divergência em `σ = ½`).
* `Biblioteca/Reducao.lean` — RH reduzida por equivalências provadas: um lado, um quarto acima de qualquer altura
  verificada, incondicional acima de 13 (`rh_iff_quarto`), o `Resto` acima de 3 000 181 942 471 com as janelas da Arb
  (`rh_reduzida`), caixas de largura `w` (`rh_iff_caixas`) e a faixa estreita com a região livre clássica
  (`rh_iff_faixa_estreita`).
* `Biblioteca/Entradas.lean` — o mapa: para cada rota, a entrada aberta e a ponte provada (`rotas_para_rh`), as
  equivalências sem hipótese (`equivalencias_sem_hipotese`), a verificação finita (`verificacao`), de Bruijn–Newman
  com Rodgers–Tao (`lambda_com_rodgers_tao`) e `rh_de_metade`.

O resto do repositório já é biblioteca: as 22 formulações equivalentes (`PontesTotal.pontes_total`), a simetria da
equação funcional (`Zeta.Symmetry`), Báez-Duarte (`BaezDuarte`), a verificação certificada até 3 000 181 222 471
como hipóteses nomeadas (`Continuacao`), os pares de Lehmer (`Lehmer`, `Alturas`) e as correções
(`Correcoes`, `Absorcao`).

**O que esta biblioteca não faz**: provar RH. Ela reduz RH a entradas abertas explícitas, com todas as pontes no
kernel; quem provar uma entrada fecha RH aqui. Nenhuma entrada é declarada como `axiom`. `OPEN_MATH = true`.
-/
