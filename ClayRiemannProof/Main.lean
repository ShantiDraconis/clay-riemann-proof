import ClayRiemann

/-!
# Hipótese de Riemann — prova

O alvo é exatamente o enunciado importado do repositório fixado em `lakefile.toml`:

    theorem main : ClayRiemann.Statement

Este repositório nunca redefine o enunciado. Enquanto não houver prova completa, este arquivo
não declara `main`: nenhum `sorry`, nenhum `axiom`.

Quando `main` existir, acrescente ao fim deste arquivo (com a saída real do Lean):

    /-- info: 'ClayRiemannProof.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
    #guard_msgs in #print axioms ClayRiemannProof.main
-/

namespace ClayRiemannProof

/-- O enunciado que a prova tem que fechar (igual por definição ao do repositório fixado). -/
abbrev Target : Prop := ClayRiemann.Statement

end ClayRiemannProof
