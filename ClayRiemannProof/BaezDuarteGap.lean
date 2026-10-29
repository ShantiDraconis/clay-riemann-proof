import ClayRiemannProof.Main
import ClayRiemannProof.BaezDuarte.Sufficiency
import ClayRiemannProof.BaezDuarte.Necessity

/-!
# O critério de Nyman–Beurling–Báez-Duarte como `Gap` exato

`Gap` é a afirmação `inf_N D_N = 0`, com `D_N` a distância de Báez-Duarte **concreta**
(`ClayRiemannProof.BaezDuarte.DN`: `χ = 𝟙_(0,1]`, `ρ_k(t) = {1/(k t)}`, integral de Lebesgue em
`(0, ∞)`). Prova-se, sem hipóteses:

* `target_of_gap : Gap → Target` (suficiência, `BaezDuarte.Sufficiency`);
* `gap_of_target : Target → Gap` (necessidade, `BaezDuarte.Necessity`: Perron suavizado, cotas de
  Titchmarsh/Lindelöf sob RH, Phragmén–Lindelöf, convergência dominada);
* `target_iff_gap : Target ↔ Gap`.

Isto é uma **equivalência**: registra exatamente o que falta (`Gap`), não prova o problema.
`OPEN_MATH = true`.

Origem: ATK kernel (espelho público), `ATK/BaezDuarteBridge.lean` (`riemann_of_iInf_zero`) e
`ATK/NecessidadeRH.lean` (`rh_iff_iInf_DN`).
-/

namespace ClayRiemannProof

open Filter Topology ClayRiemannProof.BaezDuarte

/-- **O que falta para RH, na forma de Báez-Duarte**: `inf_N D_N = 0`. -/
def Gap : Prop := (⨅ N, DN N) = 0

/-- `Gap` também se escreve `D_N → 0` (`D_N` é decrescente e limitada por baixo). -/
theorem gap_iff_tendsto : Gap ↔ Tendsto DN atTop (𝓝 0) :=
  tendsto_zero_iff_iInf_eq_zero.symm

/-- Suficiência: `Gap → Target`. -/
theorem target_of_gap (h : Gap) : Target :=
  Sufficiency.riemann_of_iInf_zero h

/-- Necessidade: `Target → Gap`. -/
theorem gap_of_target (h : Target) : Gap :=
  Necessity.rh_iff_iInf_DN.mp h

/-- **`Target ↔ Gap`** (critério de Nyman–Beurling–Báez-Duarte, completo). -/
theorem target_iff_gap : Target ↔ Gap :=
  Necessity.rh_iff_iInf_DN

end ClayRiemannProof
