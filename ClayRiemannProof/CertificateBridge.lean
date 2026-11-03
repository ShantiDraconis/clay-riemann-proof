import ClayRiemannProof.Verification
import ClayRiemannProof.CertifiedZeros.Rectangle

/-!
# Ponte explícita entre certificados de região e uma janela da zeta

Este módulo fecha a composição lógica, não fornece dados numéricos novos. Uma peça retangular
certificada por peca_ret fornece uma cota inferior positiva para |ζ| em toda a peça. Uma cobertura finita
da janela por bolas locais e peças sem zeros então prova que todo zero da janela está numa bola.
A injetividade em cada bola, combinada com a simetria s ↦ 1 − s̄, coloca esses zeros na reta.

Para instanciar o teorema são necessários dados concretos:
* centros na reta e provas de injetividade em suas bolas;
* retângulos cuja cota positiva seja derivada de certificados chkR/peca_ret;
* uma prova racional de cobertura da janela por bolas ou retângulos.

Sem esses três itens não há certificação de uma janela numérica. Em particular, este arquivo não
importa os zeros Arb como se fossem provas do kernel e não altera OPEN_MATH.
-/

namespace ClayRiemannProof.CertificateBridge

open Complex Set Metric
open ClayRiemannProof.Turing
open ClayRiemannProof.Verification
open ClayRiemannProof.CertifiedZeros.Rectangle

/-- Uma peça retangular acompanhada de uma cota inferior positiva para |ζ|. -/
structure ZeroFreeRect where
  s0 : ℚ
  s1 : ℚ
  a : ℚ
  b : ℚ
  delta : ℚ
  delta_pos : 0 < delta
  lower_bound : ∀ z : ℂ,
    z ∈ ClayRiemannProof.CertifiedZeros.Rectangle.ret s0 s1 a b →
      (delta : ℝ) ≤ ‖riemannZeta z‖

/-- A região coberta pelo certificado retangular. -/
def ZeroFreeRect.region (R : ZeroFreeRect) : Set ℂ :=
  ClayRiemannProof.CertifiedZeros.Rectangle.ret R.s0 R.s1 R.a R.b

/-- A cota positiva no retângulo exclui zeros da zeta nessa região. -/
theorem ZeroFreeRect.zeta_ne_zero (R : ZeroFreeRect) {z : ℂ}
    (hz : z ∈ R.region) : riemannZeta z ≠ 0 := by
  intro hzero
  have hbound := R.lower_bound z hz
  have hdelta : (0 : ℝ) < (R.delta : ℝ) := by exact_mod_cast R.delta_pos
  rw [hzero, norm_zero] at hbound
  linarith

/-- Uma cobertura finita de certificados locais prova a RH na janela.

hcover é a ponte de geometria/computação: todo ponto da janela está numa bola local
ou num retângulo certificado sem zeros. hcenter e hinj são as provas locais
consumidas por zero_na_bola_simetrica.
-/
theorem window_on_line_from_certificates
    {T₁ T₂ : ℝ} (B : List (ℂ × ℝ)) (R : List ZeroFreeRect)
    (hcenter : ∀ p ∈ B, p.1.re = 1 / 2)
    (hinj : ∀ p ∈ B, InjOn riemannZeta (ball p.1 p.2))
    (hcover : ∀ s : ℂ, s ∈ Janela T₁ T₂ →
      (∃ p, p ∈ B ∧ s ∈ ball p.1 p.2) ∨
      (∃ Q, Q ∈ R ∧ s ∈ Q.region)) :
    JanelaNaReta T₁ T₂ := by
  apply janelaNaReta_de_bolas B hcenter hinj
  intro s hs
  rcases hcover s hs with ⟨p, hp, hball⟩ | ⟨Q, hQ, hrect⟩
  · exact ⟨p, hp, hball⟩
  · exact False.elim (Q.zeta_ne_zero hrect hs.1)

/-- Forma para um certificado de peca_ret: sua conclusão alimenta diretamente ZeroFreeRect. -/
theorem zeroFreeRect_of_peca_ret
    (s0 s1 a b delta : ℚ)
    (hdelta : 0 < delta)
    (hpiece : ∀ z : ℂ,
      z ∈ ClayRiemannProof.CertifiedZeros.Rectangle.ret s0 s1 a b →
        (delta : ℝ) ≤ ‖riemannZeta z‖) :
    ZeroFreeRect := ⟨s0, s1, a, b, delta, hdelta, hpiece⟩

end ClayRiemannProof.CertificateBridge
