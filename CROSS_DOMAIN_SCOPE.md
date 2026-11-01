# Ponte rigorosa entre zeros, modos e estabilidade

## Parte comum que é um teorema

Para um ponto complexo (s=\sigma+it), defina a coordenada centrada

\[
\lambda=s-\tfrac12,\qquad \Re\lambda=\sigma-\tfrac12.
\]

Então, por definição,

\[
\Re s=\tfrac12 \quad\Longleftrightarrow\quad \Re\lambda=0.
\]

A reflexão funcional (s\mapsto1-s) vira (\lambda\mapsto-\lambda); a conjugação vira (\lambda\mapsto\bar\lambda). Portanto, um zero hipotético fora da linha, (s=\tfrac12+\delta+i\gamma), teria a órbita

\[
\lambda=\delta+i\gamma,\;-\delta+i\gamma,\;\delta-i\gamma,\;-\delta-i\gamma.
\]

O módulo Lean `CenteredStabilityBridge.lean` prova essa mudança de coordenadas e a equivalência entre RH e todos os zeros não triviais terem parte real centrada zero. É uma equivalência lógica; não prova RH.

## O que a comparação com sistemas dinâmicos realmente diz

Um modo (e^{\lambda t}) tem módulo (e^{(\Re\lambda)t}). Depois de centrar por (1/2), a linha crítica corresponde a modo neutro ((\Re\lambda=0)); lados opostos correspondem a crescimento e decaimento. Em estabilidade assintótica contínua, a condição usual para autovalores é (\Re\lambda<0). Logo “RH = estabilidade” só se torna uma tradução formal depois de declarar a mudança (\lambda=s-1/2), e mesmo assim é uma correspondência de coordenadas, não uma identidade física.

Em uma função de transferência, polos determinam estabilidade interna; zeros no semiplano direito podem produzir fase não mínima e resposta inversa sem, por si sós, tornar o sistema instável. Um zero de transferência não é um autovalor/polo.

## Casos de outras funções zeta

- **Davenport–Heilbronn:** há zeros off-line apesar de uma equação funcional semelhante à da zeta de Riemann. Um exemplo numérico de Spira é (0.808517+85.699348i); o reflexo em torno de (1/2) tem parte real (0.191483), não (0.4). Isso mostra que uma equação funcional sozinha não força a linha. A função não tem o produto de Euler da zeta de Riemann.
- **Epstein, (Q(m,n)=m^2+5n^2):** foi reportado um zero na faixa crítica próximo de (0.932969697+15.668249531i); a parte real refletida é (0.067030303). Para formas positivas com número de classe maior que (1), há teoremas de zeros off-line; resultados de Voronin contam zeros em subfaixas (1/2<\sigma_1<\Re s<\sigma_2<1). A hipótese é (h(D)>1), não uma regra de paridade.
- Esses exemplos vivem em funções complexas ordinárias. Não introduzem um (j) bicomplexo. A ausência de produto de Euler é uma diferença aritmética de suas séries, não uma coordenada oculta que “come” parte real.

## Outros resultados que não são a mesma estrutura

- **Lee–Yang:** para modelos de Ising ferromagnéticos sob as hipóteses do teorema, zeros no fugacidade (z) ficam no círculo (|z|=1). A variável e a simetria são diferentes de (s\mapsto1-s). O teorema não diz que qualquer antiferromagneto tem zeros em um par radial universal, nem fornece o (\delta) da zeta.
- **Selberg:** zeros espectrais da zeta de uma superfície hiperbólica relacionam-se a autovalores do Laplaciano por (\lambda=s(1-s)). Autovalores acima de (1/4) dão (s=1/2\pm it); autovalores excepcionais abaixo de (1/4) podem produzir zeros reais fora da linha. Portanto, é preciso declarar condições espectrais antes de dizer “todos os zeros não triviais estão na linha”.
- **Routh–Hurwitz:** classifica estabilidade de um sistema linear contínuo via raízes do polinômio característico no semiplano esquerdo. Não é um teorema sobre zeros de zeta, e uma raiz instável não é necessariamente um zero de função de transferência.
- **Quaternions e gimbal lock:** quatérnios usam (ij=k), (ji=-k), e evitam a singularidade de parametrização dos ângulos de Euler. Isso difere do bicomplexo com (ij=ji), (k^2=1); ((1+k)(1-k)=0) não descreve gimbal lock.

## Fórmula explícita e escala

Na fórmula explícita de \(\psi(x)\), um zero \(\rho=\beta+i\gamma\) aparece em um termo proporcional a \(x^\rho/\rho\). Comparando apenas módulos de termos à mesma altura, \(\beta=0.7\) contra \(\beta=0.5\) dá o fator \(x^{0.2}\), cerca de \(251.19\) em \(x=10^{12}\). Isso compara contribuições individuais; não é um fator exato para o erro total, que soma os termos de todos os zeros. Um zero com \(\beta>1/2\) é incompatível com erro RH de ordem \(O(x^{1/2+\varepsilon})\) para todo \(\varepsilon<\beta-1/2\).

## Fronteira da formalização

Não há uma variável universal (b) com o mesmo significado em física, química, biologia, linguagem, finanças e zeta. Cada área tem espaços de estados, unidades, operadores e teoremas próprios. Para reivindicar equivalência, seria necessário construir mapas que preservem zeros/autovalores e demonstrar hipóteses específicas em cada modelo. A identificação informal (b\neq0\Rightarrow\) “zero fora da linha” não é um teorema comum a essas disciplinas.

Esta nota e o módulo Lean não provam RH, não constroem uma zeta bicomplexa e não afirmam que zeros fora da linha da zeta de Riemann existam.
