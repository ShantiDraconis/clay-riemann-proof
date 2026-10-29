import ClayRiemannProof.BaezDuarte.Defs
import ClayRiemannProof.BaezDuarte.Faithful
import ClayRiemannProof.Zeta.Strip
import ClayRiemannProof.BaezDuarte.MellinRho
import ClayRiemannProof.BaezDuarte.NymanBeurling
import ClayRiemannProof.BaezDuarte.Sufficiency
import ClayRiemannProof.Fourier.PlancherelL1L2
import ClayRiemannProof.Fourier.MellinPlancherel
import ClayRiemannProof.BaezDuarte.Spectral
import ClayRiemannProof.BaezDuarte.NecessityFramework
import ClayRiemannProof.Zeta.Bounds
import ClayRiemannProof.Zeta.GammaVertical
import ClayRiemannProof.Zeta.LogBoundRH
import ClayRiemannProof.Zeta.Ratio
import ClayRiemannProof.Zeta.PerronSmoothed
import ClayRiemannProof.BaezDuarte.Necessity
import ClayRiemannProof.BaezDuarteGap
import ClayRiemannProof.QuasiRH

/-!
# Auditoria de axiomas

Um `#guard_msgs in #print axioms X` para cada declaração pública acrescentada (saída real do Lean).
Se aparecer qualquer axioma diferente de `propext`, `Classical.choice`, `Quot.sound` (inclusive
`sorryAx`), a compilação falha.

`Classical.choice` vem do Mathlib: `#print axioms Real` já dá `[propext, Classical.choice, Quot.sound]`.
-/


/-! ## `ClayRiemannProof/BaezDuarte/Defs.lean` -/

/-- info: 'ClayRiemannProof.BaezDuarte.chi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.chi

/-- info: 'ClayRiemannProof.BaezDuarte.rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.rho

/-- info: 'ClayRiemannProof.BaezDuarte.residualSq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.residualSq

/-- info: 'ClayRiemannProof.BaezDuarte.DN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.DN

/-- info: 'ClayRiemannProof.BaezDuarte.DN_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.DN_nonneg

/-- info: 'ClayRiemannProof.BaezDuarte.residualSq_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.residualSq_nonneg

/-- info: 'ClayRiemannProof.BaezDuarte.DN_le_residualSq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.DN_le_residualSq

/-- info: 'ClayRiemannProof.BaezDuarte.residualSq_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.residualSq_extend

/-- info: 'ClayRiemannProof.BaezDuarte.DN_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.DN_antitone

/-- info: 'ClayRiemannProof.BaezDuarte.DN_le_DN_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.DN_le_DN_zero

/-- info: 'ClayRiemannProof.BaezDuarte.DN_zero_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.DN_zero_le_one

/-- info: 'ClayRiemannProof.BaezDuarte.DN_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.DN_le_one

/-- info: 'ClayRiemannProof.BaezDuarte.DN_tendsto_iInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.DN_tendsto_iInf

/-- info: 'ClayRiemannProof.BaezDuarte.tendsto_zero_iff_iInf_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.tendsto_zero_iff_iInf_eq_zero


/-! ## `ClayRiemannProof/BaezDuarte/Faithful.lean` -/

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.rho_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.rho_nonneg

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.rho_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.rho_le_one

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.rho_le_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.rho_le_inv

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.chi_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.chi_of_mem

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.chi_of_gt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.chi_of_gt_one

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.chi_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.chi_nonneg

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.chi_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.chi_le_one

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.chi_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.chi_sq

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.measurable_rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.measurable_rho

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.measurable_chi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.measurable_chi

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.integrableOn_sq_of_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.integrableOn_sq_of_bounds

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.abs_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.abs_sum_le

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.integrable_residual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.integrable_residual

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.integrable_chi_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.integrable_chi_sq

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.integral_chi_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.integral_chi_sq

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.residualSq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.residualSq_zero

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.DN_zero_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.DN_zero_eq_one

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.rho_one_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.rho_one_pos

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.integrable_chi_rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.integrable_chi_rho

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.integrable_rho_one_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.integrable_rho_one_sq

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.integral_chi_rho_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.integral_chi_rho_pos

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.residualSq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.residualSq_one

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.DN_one_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.DN_one_lt_one

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.primeiro_delta_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.primeiro_delta_pos

/-- info: 'ClayRiemannProof.BaezDuarte.Faithful.DN_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Faithful.DN_lt_one


/-! ## `ClayRiemannProof/Zeta/Strip.lean` -/

/-- info: 'ClayRiemannProof.Zeta.Strip.fracTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Strip.fracTail

/-- info: 'ClayRiemannProof.Zeta.Strip.H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Strip.H

/-- info: 'ClayRiemannProof.Zeta.Strip.fracTail_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Strip.fracTail_norm_le

/-- info: 'ClayRiemannProof.Zeta.Strip.fracTail_of_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Strip.fracTail_of_lt_one

/-- info: 'ClayRiemannProof.Zeta.Strip.measurable_fracTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Strip.measurable_fracTail

/-- info: 'ClayRiemannProof.Zeta.Strip.locInt_fracTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Strip.locInt_fracTail

/-- info: 'ClayRiemannProof.Zeta.Strip.fracTail_isBigO_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Strip.fracTail_isBigO_top

/-- info: 'ClayRiemannProof.Zeta.Strip.fracTail_isBigO_bot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Strip.fracTail_isBigO_bot

/-- info: 'ClayRiemannProof.Zeta.Strip.mellinConvergent_fracTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Strip.mellinConvergent_fracTail

/-- info: 'ClayRiemannProof.Zeta.Strip.H_differentiableAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Strip.H_differentiableAt

/-- info: 'ClayRiemannProof.Zeta.Strip.H_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Strip.H_eq_integral

/-- info: 'ClayRiemannProof.Zeta.Strip.integrableOn_cpow_mul_fract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Strip.integrableOn_cpow_mul_fract

/-- info: 'ClayRiemannProof.Zeta.Strip.zeta_eq_mul_integral_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Strip.zeta_eq_mul_integral_floor

/-- info: 'ClayRiemannProof.Zeta.Strip.H_eq_of_one_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Strip.H_eq_of_one_lt

/-- info: 'ClayRiemannProof.Zeta.Strip.H_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Strip.H_eq

/-- info: 'ClayRiemannProof.Zeta.Strip.H_eq_zeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Strip.H_eq_zeta


/-! ## `ClayRiemannProof/BaezDuarte/MellinRho.lean` -/

/-- info: 'ClayRiemannProof.BaezDuarte.MellinRho.fr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.MellinRho.fr

/-- info: 'ClayRiemannProof.BaezDuarte.MellinRho.low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.MellinRho.low

/-- info: 'ClayRiemannProof.BaezDuarte.MellinRho.fr_decomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.MellinRho.fr_decomp

/-- info: 'ClayRiemannProof.BaezDuarte.MellinRho.ae_ne_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.MellinRho.ae_ne_one

/-- info: 'ClayRiemannProof.BaezDuarte.MellinRho.mellin_congr_ne_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.MellinRho.mellin_congr_ne_one

/-- info: 'ClayRiemannProof.BaezDuarte.MellinRho.mellinConvergent_congr_ne_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.MellinRho.mellinConvergent_congr_ne_one

/-- info: 'ClayRiemannProof.BaezDuarte.MellinRho.mellin_fr_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.MellinRho.mellin_fr_neg

/-- info: 'ClayRiemannProof.BaezDuarte.MellinRho.rho_eq_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.MellinRho.rho_eq_comp

/-- info: 'ClayRiemannProof.BaezDuarte.MellinRho.mellin_rho_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.MellinRho.mellin_rho_aux

/-- info: 'ClayRiemannProof.BaezDuarte.MellinRho.mellin_rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.MellinRho.mellin_rho

/-- info: 'ClayRiemannProof.BaezDuarte.MellinRho.mellinConvergent_rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.MellinRho.mellinConvergent_rho

/-- info: 'ClayRiemannProof.BaezDuarte.MellinRho.mellin_rho_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.MellinRho.mellin_rho_eq_zero


/-! ## `ClayRiemannProof/BaezDuarte/Sufficiency.lean` -/

/-- info: 'ClayRiemannProof.BaezDuarte.Sufficiency.chi_complex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Sufficiency.chi_complex

/-- info: 'ClayRiemannProof.BaezDuarte.Sufficiency.hasMellin_chi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Sufficiency.hasMellin_chi

/-- info: 'ClayRiemannProof.BaezDuarte.Sufficiency.res' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Sufficiency.res

/-- info: 'ClayRiemannProof.BaezDuarte.Sufficiency.tailS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Sufficiency.tailS

/-- info: 'ClayRiemannProof.BaezDuarte.Sufficiency.residualSq_eq_res' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Sufficiency.residualSq_eq_res

/-- info: 'ClayRiemannProof.BaezDuarte.Sufficiency.integrable_res_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Sufficiency.integrable_res_sq

/-- info: 'ClayRiemannProof.BaezDuarte.Sufficiency.mellin_res' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Sufficiency.mellin_res

/-- info: 'ClayRiemannProof.BaezDuarte.Sufficiency.norm_mellin_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Sufficiency.norm_mellin_le

/-- info: 'ClayRiemannProof.BaezDuarte.Sufficiency.rho_of_gt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Sufficiency.rho_of_gt_one

/-- info: 'ClayRiemannProof.BaezDuarte.Sufficiency.res_of_gt_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Sufficiency.res_of_gt_one

/-- info: 'ClayRiemannProof.BaezDuarte.Sufficiency.integral_tail_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Sufficiency.integral_tail_sq

/-- info: 'ClayRiemannProof.BaezDuarte.Sufficiency.tailS_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Sufficiency.tailS_sq_le

/-- info: 'ClayRiemannProof.BaezDuarte.Sufficiency.integral_tail_weighted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Sufficiency.integral_tail_weighted

/-- info: 'ClayRiemannProof.BaezDuarte.Sufficiency.amgm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Sufficiency.amgm

/-- info: 'ClayRiemannProof.BaezDuarte.Sufficiency.integral_rpow_Ioc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Sufficiency.integral_rpow_Ioc

/-- info: 'ClayRiemannProof.BaezDuarte.Sufficiency.integrableOn_rpow_Ioc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Sufficiency.integrableOn_rpow_Ioc

/-- info: 'ClayRiemannProof.BaezDuarte.Sufficiency.integral_head_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Sufficiency.integral_head_le

/-- info: 'ClayRiemannProof.BaezDuarte.Sufficiency.key_ineq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Sufficiency.key_ineq

/-- info: 'ClayRiemannProof.BaezDuarte.Sufficiency.zeta_ne_zero_strip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Sufficiency.zeta_ne_zero_strip

/-- info: 'ClayRiemannProof.BaezDuarte.Sufficiency.riemannHypothesis_of_strip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Sufficiency.riemannHypothesis_of_strip

/-- info: 'ClayRiemannProof.BaezDuarte.Sufficiency.baezDuarte_sufficiency' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Sufficiency.baezDuarte_sufficiency

/-- info: 'ClayRiemannProof.BaezDuarte.Sufficiency.riemann_of_iInf_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Sufficiency.riemann_of_iInf_zero


/-! ## `ClayRiemannProof/Fourier/PlancherelL1L2.lean` -/

/-- info: 'ClayRiemannProof.Fourier.PlancherelL1L2.continuous_fourier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fourier.PlancherelL1L2.continuous_fourier

/-- info: 'ClayRiemannProof.Fourier.PlancherelL1L2.integral_fourier_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fourier.PlancherelL1L2.integral_fourier_mul

/-- info: 'ClayRiemannProof.Fourier.PlancherelL1L2.fourier_toLp_ae_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fourier.PlancherelL1L2.fourier_toLp_ae_eq

/-- info: 'ClayRiemannProof.Fourier.PlancherelL1L2.memLp_two_fourier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fourier.PlancherelL1L2.memLp_two_fourier

/-- info: 'ClayRiemannProof.Fourier.PlancherelL1L2.norm_sq_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fourier.PlancherelL1L2.norm_sq_eq_integral

/-- info: 'ClayRiemannProof.Fourier.PlancherelL1L2.integral_norm_sq_fourier' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fourier.PlancherelL1L2.integral_norm_sq_fourier


/-! ## `ClayRiemannProof/Fourier/MellinPlancherel.lean` -/

/-- info: 'ClayRiemannProof.Fourier.MellinPlancherel.rexp_neg_deriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fourier.MellinPlancherel.rexp_neg_deriv

/-- info: 'ClayRiemannProof.Fourier.MellinPlancherel.rexp_neg_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fourier.MellinPlancherel.rexp_neg_image

/-- info: 'ClayRiemannProof.Fourier.MellinPlancherel.rexp_neg_injOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fourier.MellinPlancherel.rexp_neg_injOn

/-- info: 'ClayRiemannProof.Fourier.MellinPlancherel.lado' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fourier.MellinPlancherel.lado

/-- info: 'ClayRiemannProof.Fourier.MellinPlancherel.integral_Ioi_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fourier.MellinPlancherel.integral_Ioi_eq

/-- info: 'ClayRiemannProof.Fourier.MellinPlancherel.integrableOn_Ioi_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fourier.MellinPlancherel.integrableOn_Ioi_iff

/-- info: 'ClayRiemannProof.Fourier.MellinPlancherel.norm_sq_lado' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fourier.MellinPlancherel.norm_sq_lado

/-- info: 'ClayRiemannProof.Fourier.MellinPlancherel.integrable_lado' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fourier.MellinPlancherel.integrable_lado

/-- info: 'ClayRiemannProof.Fourier.MellinPlancherel.fourier_lado' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fourier.MellinPlancherel.fourier_lado

/-- info: 'ClayRiemannProof.Fourier.MellinPlancherel.integral_norm_sq_eq_mellin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fourier.MellinPlancherel.integral_norm_sq_eq_mellin


/-! ## `ClayRiemannProof/BaezDuarte/Spectral.lean` -/

/-- info: 'ClayRiemannProof.BaezDuarte.Spectral.espectro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Spectral.espectro

/-- info: 'ClayRiemannProof.BaezDuarte.Spectral.mellin_res_geral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Spectral.mellin_res_geral

/-- info: 'ClayRiemannProof.BaezDuarte.Spectral.residualSq_espectral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Spectral.residualSq_espectral

/-- info: 'ClayRiemannProof.BaezDuarte.Spectral.DN_espectral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Spectral.DN_espectral

/-- info: 'ClayRiemannProof.BaezDuarte.Spectral.DNespectral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Spectral.DNespectral

/-- info: 'ClayRiemannProof.BaezDuarte.Spectral.DN_eq_DNespectral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Spectral.DN_eq_DNespectral

/-- info: 'ClayRiemannProof.BaezDuarte.Spectral.necessidade_iff_espectral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Spectral.necessidade_iff_espectral

/-- info: 'ClayRiemannProof.BaezDuarte.Spectral.rh_of_espectral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Spectral.rh_of_espectral


/-! ## `ClayRiemannProof/BaezDuarte/NecessityFramework.lean` -/

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.lc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.lc

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.lc_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.lc_re

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.lc_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.lc_ne_zero

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.continuous_lc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.continuous_lc

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.integrable_mellin_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.integrable_mellin_sq

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.integrable_espectro' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.integrable_espectro

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.integrable_inv_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.integrable_inv_sq

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.integrable_one_add_zeta_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.integrable_one_add_zeta_sq

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.continuous_zeta_lc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.continuous_zeta_lc

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.integrable_zeta_sq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.integrable_zeta_sq

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.polD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.polD

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.erro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.erro

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.erro_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.erro_nonneg

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.espectro_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.espectro_neg

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.iInf_DN_le_of_aprox' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.iInf_DN_le_of_aprox

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.DN_tendsto_zero_of_aprox' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.DN_tendsto_zero_of_aprox

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.moll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.moll

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.J' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.J

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.polD_moll_eq_term' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.polD_moll_eq_term

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.tendsto_polD_moll' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.tendsto_polD_moll

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.norm_polD_moll_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.norm_polD_moll_le

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.EntradaLittlewood' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.EntradaLittlewood

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.entradaLittlewood_of_gt_half' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.entradaLittlewood_of_gt_half

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.iInf_DN_le_J' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.iInf_DN_le_J

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.iInf_DN_le_J_of_gt_half' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.iInf_DN_le_J_of_gt_half

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.EntradasNecessidade' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.EntradasNecessidade

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.DN_tendsto_zero_of_entradas' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.DN_tendsto_zero_of_entradas

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.necessidade_de_entradas' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.necessidade_de_entradas

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.rh_iff_DN_of_entradas' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.rh_iff_DN_of_entradas

/-- info: 'ClayRiemannProof.BaezDuarte.NecessityFramework.rh_of_entradas' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NecessityFramework.rh_of_entradas


/-! ## `ClayRiemannProof/Zeta/Bounds.lean` -/

/-- info: 'ClayRiemannProof.Zeta.Bounds.Hr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Bounds.Hr

/-- info: 'ClayRiemannProof.Zeta.Bounds.g' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Bounds.g

/-- info: 'ClayRiemannProof.Zeta.Bounds.norm_H_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Bounds.norm_H_le

/-- info: 'ClayRiemannProof.Zeta.Bounds.integrableOn_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Bounds.integrableOn_rpow

/-- info: 'ClayRiemannProof.Zeta.Bounds.integrableOn_g' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Bounds.integrableOn_g

/-- info: 'ClayRiemannProof.Zeta.Bounds.integral_rpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Bounds.integral_rpow

/-- info: 'ClayRiemannProof.Zeta.Bounds.Hr_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Bounds.Hr_eq

/-- info: 'ClayRiemannProof.Zeta.Bounds.fract_on' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Bounds.fract_on

/-- info: 'ClayRiemannProof.Zeta.Bounds.intervalIntegrable_g' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Bounds.intervalIntegrable_g

/-- info: 'ClayRiemannProof.Zeta.Bounds.peca_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Bounds.peca_nonpos

/-- info: 'ClayRiemannProof.Zeta.Bounds.integral_g_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Bounds.integral_g_nonpos

/-- info: 'ClayRiemannProof.Zeta.Bounds.Hr_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Bounds.Hr_le

/-- info: 'ClayRiemannProof.Zeta.Bounds.zeta_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Bounds.zeta_eq

/-- info: 'ClayRiemannProof.Zeta.Bounds.norm_zeta_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Bounds.norm_zeta_le


/-! ## `ClayRiemannProof/Zeta/GammaVertical.lean` -/

/-- info: 'ClayRiemannProof.Zeta.GammaVertical.norm_Gamma_le_Gamma_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.GammaVertical.norm_Gamma_le_Gamma_re

/-- info: 'ClayRiemannProof.Zeta.GammaVertical.Gamma_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.GammaVertical.Gamma_le_two

/-- info: 'ClayRiemannProof.Zeta.GammaVertical.norm_cos_le_cosh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.GammaVertical.norm_cos_le_cosh

/-- info: 'ClayRiemannProof.Zeta.GammaVertical.cosh_le_exp_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.GammaVertical.cosh_le_exp_abs

/-- info: 'ClayRiemannProof.Zeta.GammaVertical.exp_abs_le_two_cosh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.GammaVertical.exp_abs_le_two_cosh

/-- info: 'ClayRiemannProof.Zeta.GammaVertical.norm_sq_Gamma_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.GammaVertical.norm_sq_Gamma_half

/-- info: 'ClayRiemannProof.Zeta.GammaVertical.norm_Gamma_half_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.GammaVertical.norm_Gamma_half_le

/-- info: 'ClayRiemannProof.Zeta.GammaVertical.Hst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.GammaVertical.Hst

/-- info: 'ClayRiemannProof.Zeta.GammaVertical.arg_mul_im_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.GammaVertical.arg_mul_im_bounds

/-- info: 'ClayRiemannProof.Zeta.GammaVertical.norm_cpow_half_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.GammaVertical.norm_cpow_half_sub

/-- info: 'ClayRiemannProof.Zeta.GammaVertical.norm_Hst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.GammaVertical.norm_Hst

/-- info: 'ClayRiemannProof.Zeta.GammaVertical.differentiableAt_Hst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.GammaVertical.differentiableAt_Hst

/-- info: 'ClayRiemannProof.Zeta.GammaVertical.norm_Hst_borda_esq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.GammaVertical.norm_Hst_borda_esq

/-- info: 'ClayRiemannProof.Zeta.GammaVertical.norm_Hst_borda_dir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.GammaVertical.norm_Hst_borda_dir

/-- info: 'ClayRiemannProof.Zeta.GammaVertical.norm_Hst_le_faixa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.GammaVertical.norm_Hst_le_faixa

/-- info: 'ClayRiemannProof.Zeta.GammaVertical.re_add_im_I' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.GammaVertical.re_add_im_I

/-- info: 'ClayRiemannProof.Zeta.GammaVertical.norm_Hst_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.GammaVertical.norm_Hst_le

/-- info: 'ClayRiemannProof.Zeta.GammaVertical.CΓ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.GammaVertical.CΓ

/-- info: 'ClayRiemannProof.Zeta.GammaVertical.CΓ_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.GammaVertical.CΓ_pos

/-- info: 'ClayRiemannProof.Zeta.GammaVertical.norm_Gamma_le_vertical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.GammaVertical.norm_Gamma_le_vertical

/-- info: 'ClayRiemannProof.Zeta.GammaVertical.norm_zeta_one_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.GammaVertical.norm_zeta_one_sub_le


/-! ## `ClayRiemannProof/Zeta/LogBoundRH.lean` -/

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.zeta_ne_zero_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.zeta_ne_zero_of_RH

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.zeta₁_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.zeta₁_eq

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.zeta₁_ne_zero_of_RH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.zeta₁_ne_zero_of_RH

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.F

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.F_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.F_eq

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.differentiableAt_F' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.differentiableAt_F

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.existe_log_bola' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.existe_log_bola

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.tres_circulos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.tres_circulos

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.soma_inv_sq_add_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.soma_inv_sq_add_two

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.norm_zeta_sub_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.norm_zeta_sub_one_le

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.zeta_ne_zero_re_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.zeta_ne_zero_re_ge

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.norm_log_zeta_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.norm_log_zeta_le

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.norm_inv_zeta_le_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.norm_inv_zeta_le_two

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.young' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.young

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.c₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.c₀

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.c₀_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.c₀_re

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.c₀_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.c₀_im

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.bola_props' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.bola_props

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.norm_zeta_le_bola' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.norm_zeta_le_bola

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.log_zeta_c₀' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.log_zeta_c₀

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.existe_log_zeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.existe_log_zeta

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.θ₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.θ₂

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.θ₂_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.θ₂_bounds

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.L_eq_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.L_eq_log

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.norm_L_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.norm_L_le

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.norm_F_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.norm_F_le

/-- info: 'ClayRiemannProof.Zeta.LogBoundRH.norm_zeta_le_RH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.LogBoundRH.norm_zeta_le_RH


/-! ## `ClayRiemannProof/Zeta/Ratio.lean` -/

/-- info: 'ClayRiemannProof.Zeta.Ratio.E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Ratio.E

/-- info: 'ClayRiemannProof.Zeta.Ratio.norm_zeta₁_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Ratio.norm_zeta₁_le

/-- info: 'ClayRiemannProof.Zeta.Ratio.norm_peso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Ratio.norm_peso

/-- info: 'ClayRiemannProof.Zeta.Ratio.differentiableAt_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Ratio.differentiableAt_E

/-- info: 'ClayRiemannProof.Zeta.Ratio.E_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Ratio.E_eq

/-- info: 'ClayRiemannProof.Zeta.Ratio.norm_E_esq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Ratio.norm_E_esq

/-- info: 'ClayRiemannProof.Zeta.Ratio.norm_E_dir' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Ratio.norm_E_dir

/-- info: 'ClayRiemannProof.Zeta.Ratio.CE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Ratio.CE

/-- info: 'ClayRiemannProof.Zeta.Ratio.CE_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Ratio.CE_pos

/-- info: 'ClayRiemannProof.Zeta.Ratio.norm_E_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Ratio.norm_E_le

/-- info: 'ClayRiemannProof.Zeta.Ratio.norm_razao_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Ratio.norm_razao_le


/-! ## `ClayRiemannProof/Zeta/PerronSmoothed.lean` -/

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.desloca' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.desloca

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.kk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.kk

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.KK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.KK

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.continuous_kk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.continuous_kk

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.kk_of_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.kk_of_le_one

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.kk_of_one_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.kk_of_one_le

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.kk_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.kk_nonneg

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.kk_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.kk_le_one

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.integral_zero_one_cpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.integral_zero_one_cpow

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.integrableOn_cpow_Ioc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.integrableOn_cpow_Ioc

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.cpow_eq_mul_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.cpow_eq_mul_self

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.intervalIntegrable_cpow01' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.intervalIntegrable_cpow01

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.mellin_kk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.mellin_kk

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.mellinConvergent_kk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.mellinConvergent_kk

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.mellin_kk_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.mellin_kk_sub

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.mellinConvergent_kk_sub' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.mellinConvergent_kk_sub

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.norm_KK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.norm_KK

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.sq_norm_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.sq_norm_line

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.le_of_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.le_of_sq_le

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.norm_KK_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.norm_KK_le

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.continuous_KK_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.continuous_KK_line

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.integrable_KK_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.integrable_KK_line

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.perron_kk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.perron_kk

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.integral_KK_um' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.integral_KK_um

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.integral_KK_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.integral_KK_neg

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.AN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.AN

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.hasSum_moebius' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.hasSum_moebius

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.cpow_quociente' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.cpow_quociente

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.integrable_perron' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.integrable_perron

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.integral_termo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.integral_termo

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.AN_eq_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.AN_eq_integral

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.phi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.phi

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.H1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.H1

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.phi_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.phi_zero

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.H1_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.H1_eq

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.differentiableAt_phi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.differentiableAt_phi

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.differentiableAt_H1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.differentiableAt_H1

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.norm_phi_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.norm_phi_le

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.peso_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.peso_le

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.re_linha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.re_linha

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.im_linha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.im_linha

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.norm_linha_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.norm_linha_le

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.integrable_peso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.integrable_peso

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.continuous_phi_linha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.continuous_phi_linha

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.integrable_linha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.integrable_linha

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.norm_H1_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.norm_H1_le

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.desloca_AN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.desloca_AN

/-- info: 'ClayRiemannProof.Zeta.PerronSmoothed.norm_AN_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.PerronSmoothed.norm_AN_sub_le


/-! ## `ClayRiemannProof/BaezDuarte/Necessity.lean` -/

/-- info: 'ClayRiemannProof.BaezDuarte.Necessity.iInf_DN_le_of_aprox_var' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Necessity.iInf_DN_le_of_aprox_var

/-- info: 'ClayRiemannProof.BaezDuarte.Necessity.mollS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Necessity.mollS

/-- info: 'ClayRiemannProof.BaezDuarte.Necessity.polD_mollS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Necessity.polD_mollS

/-- info: 'ClayRiemannProof.BaezDuarte.Necessity.norm_lc_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Necessity.norm_lc_sq

/-- info: 'ClayRiemannProof.BaezDuarte.Necessity.um_add_abs_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Necessity.um_add_abs_sq_le

/-- info: 'ClayRiemannProof.BaezDuarte.Necessity.erro_le_de' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Necessity.erro_le_de

/-- info: 'ClayRiemannProof.BaezDuarte.Necessity.integrable_cota' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Necessity.integrable_cota

/-- info: 'ClayRiemannProof.BaezDuarte.Necessity.norm_razao_rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Necessity.norm_razao_rho

/-- info: 'ClayRiemannProof.BaezDuarte.Necessity.lc_add_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Necessity.lc_add_re

/-- info: 'ClayRiemannProof.BaezDuarte.Necessity.lc_add_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Necessity.lc_add_im

/-- info: 'ClayRiemannProof.BaezDuarte.Necessity.rho_pows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Necessity.rho_pows

/-- info: 'ClayRiemannProof.BaezDuarte.Necessity.iInf_DN_le_J_RH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Necessity.iInf_DN_le_J_RH

/-- info: 'ClayRiemannProof.BaezDuarte.Necessity.lc_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Necessity.lc_injective

/-- info: 'ClayRiemannProof.BaezDuarte.Necessity.countable_zeros_lc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Necessity.countable_zeros_lc

/-- info: 'ClayRiemannProof.BaezDuarte.Necessity.ae_zeta_lc_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Necessity.ae_zeta_lc_ne_zero

/-- info: 'ClayRiemannProof.BaezDuarte.Necessity.continuous_zeta_lc_add' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Necessity.continuous_zeta_lc_add

/-- info: 'ClayRiemannProof.BaezDuarte.Necessity.tendsto_J_RH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Necessity.tendsto_J_RH

/-- info: 'ClayRiemannProof.BaezDuarte.Necessity.necessidade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Necessity.necessidade

/-- info: 'ClayRiemannProof.BaezDuarte.Necessity.rh_iff_DN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Necessity.rh_iff_DN

/-- info: 'ClayRiemannProof.BaezDuarte.Necessity.rh_iff_iInf_DN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.Necessity.rh_iff_iInf_DN


/-! ## `ClayRiemannProof/BaezDuarteGap.lean` -/

/-- info: 'ClayRiemannProof.Gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Gap

/-- info: 'ClayRiemannProof.gap_iff_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.gap_iff_tendsto

/-- info: 'ClayRiemannProof.target_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.target_of_gap

/-- info: 'ClayRiemannProof.gap_of_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.gap_of_target

/-- info: 'ClayRiemannProof.target_iff_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.target_iff_gap


/-! ## `ClayRiemannProof/QuasiRH.lean` -/

/-- info: 'ClayRiemannProof.OpenAIQuasiRH78' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.OpenAIQuasiRH78

/-- info: 'ClayRiemannProof.NoZero_half_78' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.NoZero_half_78

/-- info: 'ClayRiemannProof.NoZero_right_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.NoZero_right_half

/-- info: 'ClayRiemannProof.not_trivial_of_re_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.not_trivial_of_re_pos

/-- info: 'ClayRiemannProof.riemannZeta_one_sub_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.riemannZeta_one_sub_eq_zero

/-- info: 'ClayRiemannProof.target_iff_noZero_right_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.target_iff_noZero_right_half

/-- info: 'ClayRiemannProof.openAIQuasiRH78_of_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.openAIQuasiRH78_of_target

/-- info: 'ClayRiemannProof.target_iff_noZero_half_78' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.target_iff_noZero_half_78

/-! ## `ClayRiemannProof/BaezDuarte/NymanBeurling.lean` -/

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.rhoθ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.rhoθ

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.fθ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.fθ

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.rhoθ_eq_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.rhoθ_eq_comp

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.cpow_inv_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.cpow_inv_neg

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.mellin_rhoθ_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.mellin_rhoθ_aux

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.mellinConvergent_rhoθ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.mellinConvergent_rhoθ

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.mellin_rhoθ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.mellin_rhoθ

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.fθ_eq_zero_of_one_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.fθ_eq_zero_of_one_lt

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.fθ_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.fθ_eq

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.mellinConvergent_fθ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.mellinConvergent_fθ

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.mellin_fθ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.mellin_fθ

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.mellin_fθ_eq_integral_Ioc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.mellin_fθ_eq_integral_Ioc

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.integral_Ioc_fθ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.integral_Ioc_fθ

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.integral_Ioc_fθ_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.integral_Ioc_fθ_eq_zero
