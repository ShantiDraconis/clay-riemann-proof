# Escopo da formalização bicomplexa

Esta alteração acrescenta dois módulos Lean ao repositório:

- `ClayRiemannProof/BicomplexCoordinates.lean`: verifica identidades algébricas em quatro coordenadas inteiras para (i^2=j^2=-1), (ij=ji=k), (k^2=1), os divisores de zero (1+k) e (1-k), e as contas de coordenadas reais.
- `ClayRiemannProof/BicomplexConditional.lean`: formaliza uma ponte **condicional** para as componentes idempotentes. Se ambas as componentes (\sigma+b+it) e (\sigma-b+it) forem zeros ordinários de zeta dentro da faixa crítica e uma hipótese RH para esses zeros der parte real (1/2), então (\sigma=1/2) e (b=0).

A segunda conclusão depende da hipótese aplicada às duas componentes. Um único componente com parte real (1/2) não determina (b=0); o módulo inclui um contraexemplo puramente coordenado. O código não constrói uma continuação analítica bicomplexa da função zeta nem prova que um zero de uma eventual extensão corresponda a dois zeros clássicos. Essa é uma ponte matemática ainda em aberto.

Na álgebra bicomplexa, ((1+k)(1-k)=0) com fatores não nulos significa que eles são divisores de zero. Isso não significa que uma função seja zero quando apenas uma projeção idempotente se anula: o elemento bicomplexo é zero quando as duas componentes se anulam.

Também não há um “inteiro depois do infinito” no sistema padrão dos naturais: o módulo `FiniteWorlds` prova que não existe último natural. Qualquer formalização de um truncamento após todos os naturais precisaria especificar outro sistema, por exemplo uma extensão não padrão, e seus axiomas.

O CI do repositório compila esses módulos com Lean/Mathlib. Uma compilação bem-sucedida só verifica as declarações formais acima; não transforma a hipótese RH nem as pontes ausentes em teoremas.
