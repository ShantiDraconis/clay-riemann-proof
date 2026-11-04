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
import ClayRiemannProof.Zeta.Symmetry
import ClayRiemannProof.FiniteWorlds
import ClayRiemannProof.HyperTruncation
import ClayRiemannProof.Bicomplex
import ClayRiemannProof.Locks
import ClayRiemannProof.Bridges
import ClayRiemannProof.TresTravas
import ClayRiemannProof.Analogs
import ClayRiemannProof.Fronteira.Clay
import ClayRiemannProof.LiFinite
import ClayRiemannProof.Turing
import ClayRiemannProof.Xi
import ClayRiemannProof.LiCircle
import ClayRiemannProof.Colisao
import ClayRiemannProof.QuartetoForcado
import ClayRiemannProof.Verification
import ClayRiemannProof.BicomplexCoordinates
import ClayRiemannProof.BicomplexConditional
import ClayRiemannProof.CenteredStabilityBridge
import ClayRiemannProof.PrimeiroFora
import ClayRiemannProof.PontesTotal
import ClayRiemannProof.Lehmer
import ClayRiemannProof.Paridade
import ClayRiemannProof.Gram
import ClayRiemannProof.QuartetoDesenhado
import ClayRiemannProof.Continuacao
import ClayRiemannProof.Alturas
import ClayRiemannProof.Forca
import ClayRiemannProof.Empurrao
import ClayRiemannProof.Leis
import ClayRiemannProof.Correcoes
import ClayRiemannProof.Absorcao

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

/-! ## `ClayRiemannProof/Zeta/Symmetry.lean` -/

/-- info: 'ClayRiemannProof.Zeta.Symmetry.tensao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.tensao

/-- info: 'ClayRiemannProof.Zeta.Symmetry.espelho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.espelho

/-- info: 'ClayRiemannProof.Zeta.Symmetry.torcao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.torcao

/-- info: 'ClayRiemannProof.Zeta.Symmetry.compressao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.compressao

/-- info: 'ClayRiemannProof.Zeta.Symmetry.tensao_tensao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.tensao_tensao

/-- info: 'ClayRiemannProof.Zeta.Symmetry.espelho_espelho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.espelho_espelho

/-- info: 'ClayRiemannProof.Zeta.Symmetry.torcao_torcao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.torcao_torcao

/-- info: 'ClayRiemannProof.Zeta.Symmetry.torcao_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.torcao_eq

/-- info: 'ClayRiemannProof.Zeta.Symmetry.tensao_fixo_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.tensao_fixo_iff

/-- info: 'ClayRiemannProof.Zeta.Symmetry.espelho_fixo_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.espelho_fixo_iff

/-- info: 'ClayRiemannProof.Zeta.Symmetry.torcao_fixo_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.torcao_fixo_iff

/-- info: 'ClayRiemannProof.Zeta.Symmetry.re_tensao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.re_tensao

/-- info: 'ClayRiemannProof.Zeta.Symmetry.re_torcao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.re_torcao

/-- info: 'ClayRiemannProof.Zeta.Symmetry.re_compressao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.re_compressao

/-- info: 'ClayRiemannProof.Zeta.Symmetry.compressao_neutro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.compressao_neutro

/-- info: 'ClayRiemannProof.Zeta.Symmetry.compressao_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.compressao_comp

/-- info: 'ClayRiemannProof.Zeta.Symmetry.compressao_tensao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.compressao_tensao

/-- info: 'ClayRiemannProof.Zeta.Symmetry.rigidez_neutro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.rigidez_neutro

/-- info: 'ClayRiemannProof.Zeta.Symmetry.Trivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.Trivial

/-- info: 'ClayRiemannProof.Zeta.Symmetry.re_trivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.re_trivial

/-- info: 'ClayRiemannProof.Zeta.Symmetry.nao_neg_nat_of_re_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.nao_neg_nat_of_re_pos

/-- info: 'ClayRiemannProof.Zeta.Symmetry.zero_trivial_de_re_nao_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.zero_trivial_de_re_nao_pos

/-- info: 'ClayRiemannProof.Zeta.Symmetry.zero_na_faixa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.zero_na_faixa

/-- info: 'ClayRiemannProof.Zeta.Symmetry.Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.Z

/-- info: 'ClayRiemannProof.Zeta.Symmetry.mem_Z_iff_nao_trivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.mem_Z_iff_nao_trivial

/-- info: 'ClayRiemannProof.Zeta.Symmetry.tensao_mem_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.tensao_mem_Z

/-- info: 'ClayRiemannProof.Zeta.Symmetry.espelho_mem_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.espelho_mem_Z

/-- info: 'ClayRiemannProof.Zeta.Symmetry.torcao_mem_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.torcao_mem_Z

/-- info: 'ClayRiemannProof.Zeta.Symmetry.H_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.H_real

/-- info: 'ClayRiemannProof.Zeta.Symmetry.H_real_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.H_real_nonneg

/-- info: 'ClayRiemannProof.Zeta.Symmetry.zeta_real_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.zeta_real_neg

/-- info: 'ClayRiemannProof.Zeta.Symmetry.zeta_ne_zero_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.zeta_ne_zero_real

/-- info: 'ClayRiemannProof.Zeta.Symmetry.zeta_meio_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.zeta_meio_neg

/-- info: 'ClayRiemannProof.Zeta.Symmetry.im_ne_zero_of_mem_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.im_ne_zero_of_mem_Z

/-- info: 'ClayRiemannProof.Zeta.Symmetry.quarteto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.quarteto

/-- info: 'ClayRiemannProof.Zeta.Symmetry.FimLivre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.FimLivre

/-- info: 'ClayRiemannProof.Zeta.Symmetry.InicioLivre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.InicioLivre

/-- info: 'ClayRiemannProof.Zeta.Symmetry.fimLivre_um' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.fimLivre_um

/-- info: 'ClayRiemannProof.Zeta.Symmetry.inicioLivre_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.inicioLivre_zero

/-- info: 'ClayRiemannProof.Zeta.Symmetry.fimLivre_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.fimLivre_mono

/-- info: 'ClayRiemannProof.Zeta.Symmetry.inicioLivre_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.inicioLivre_mono

/-- info: 'ClayRiemannProof.Zeta.Symmetry.fim_iff_inicio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.fim_iff_inicio

/-- info: 'ClayRiemannProof.Zeta.Symmetry.riemann_imp_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.riemann_imp_re

/-- info: 'ClayRiemannProof.Zeta.Symmetry.riemann_iff_fim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.riemann_iff_fim

/-- info: 'ClayRiemannProof.Zeta.Symmetry.riemann_iff_inicio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.riemann_iff_inicio

/-- info: 'ClayRiemannProof.Zeta.Symmetry.uniao_fins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.uniao_fins

/-- info: 'ClayRiemannProof.Zeta.Symmetry.uniao_inicios' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.uniao_inicios

/-- info: 'ClayRiemannProof.Zeta.Symmetry.riemann_iff_torcao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.riemann_iff_torcao

/-- info: 'ClayRiemannProof.Zeta.Symmetry.riemann_iff_compressao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.riemann_iff_compressao

/-- info: 'ClayRiemannProof.Zeta.Symmetry.colar_meio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.colar_meio

/-- info: 'ClayRiemannProof.Zeta.Symmetry.riemann_iff_colares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Zeta.Symmetry.riemann_iff_colares

/-! ## `ClayRiemannProof/FiniteWorlds.lean` -/

/-- info: 'ClayRiemannProof.FiniteWorlds.Sat' does not depend on any axioms -/
#guard_msgs in #print axioms ClayRiemannProof.FiniteWorlds.Sat

/-- info: 'ClayRiemannProof.FiniteWorlds.satAdd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.FiniteWorlds.satAdd

/-- info: 'ClayRiemannProof.FiniteWorlds.le_ultimo' does not depend on any axioms -/
#guard_msgs in #print axioms ClayRiemannProof.FiniteWorlds.le_ultimo

/-- info: 'ClayRiemannProof.FiniteWorlds.ultimo_absorve' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.FiniteWorlds.ultimo_absorve

/-- info: 'ClayRiemannProof.FiniteWorlds.satAdd_comm' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.FiniteWorlds.satAdd_comm

/-- info: 'ClayRiemannProof.FiniteWorlds.satAdd_assoc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.FiniteWorlds.satAdd_assoc

/-- info: 'ClayRiemannProof.FiniteWorlds.cancelamento_falha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.FiniteWorlds.cancelamento_falha

/-- info: 'ClayRiemannProof.FiniteWorlds.nao_ha_ultimo_inteiro' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.FiniteWorlds.nao_ha_ultimo_inteiro

/-- info: 'ClayRiemannProof.FiniteWorlds.RHateZ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.FiniteWorlds.RHateZ

/-- info: 'ClayRiemannProof.FiniteWorlds.RHnoMundo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.FiniteWorlds.RHnoMundo

/-- info: 'ClayRiemannProof.FiniteWorlds.RHateZ_anti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.FiniteWorlds.RHateZ_anti

/-- info: 'ClayRiemannProof.FiniteWorlds.rhNoMundo_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.FiniteWorlds.rhNoMundo_iff

/-- info: 'ClayRiemannProof.FiniteWorlds.target_iff_todos_os_mundos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.FiniteWorlds.target_iff_todos_os_mundos

/-- info: 'ClayRiemannProof.FiniteWorlds.not_target_iff_um_mundo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.FiniteWorlds.not_target_iff_um_mundo

/-- info: 'ClayRiemannProof.FiniteWorlds.rhNoMundo_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.FiniteWorlds.rhNoMundo_zero

/-- info: 'ClayRiemannProof.FiniteWorlds.PlattTrudgian2021' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.FiniteWorlds.PlattTrudgian2021

/-- info: 'ClayRiemannProof.FiniteWorlds.rhNoMundo_platt_trudgian' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.FiniteWorlds.rhNoMundo_platt_trudgian

/-! ## `ClayRiemannProof/HyperTruncation.lean` -/

/-- info: 'ClayRiemannProof.HyperTruncation.DOmega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.HyperTruncation.DOmega

/-- info: 'ClayRiemannProof.HyperTruncation.IsInfinitesimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.HyperTruncation.IsInfinitesimal

/-- info: 'ClayRiemannProof.HyperTruncation.DOmega_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.HyperTruncation.DOmega_nonneg

/-- info: 'ClayRiemannProof.HyperTruncation.target_iff_DOmega_infinitesimal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.HyperTruncation.target_iff_DOmega_infinitesimal

/-- info: 'ClayRiemannProof.HyperTruncation.nat_lt_omega' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.HyperTruncation.nat_lt_omega

/-- info: 'ClayRiemannProof.HyperTruncation.nat_lt_omega_sub_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.HyperTruncation.nat_lt_omega_sub_one

/-! ## `ClayRiemannProof/Bicomplex.lean` -/

/-- info: 'ClayRiemannProof.Bicomplex.BC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.BC

/-- info: 'ClayRiemannProof.Bicomplex.zero_c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.zero_c1

/-- info: 'ClayRiemannProof.Bicomplex.zero_c2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.zero_c2

/-- info: 'ClayRiemannProof.Bicomplex.one_c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.one_c1

/-- info: 'ClayRiemannProof.Bicomplex.one_c2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.one_c2

/-- info: 'ClayRiemannProof.Bicomplex.add_c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.add_c1

/-- info: 'ClayRiemannProof.Bicomplex.add_c2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.add_c2

/-- info: 'ClayRiemannProof.Bicomplex.neg_c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.neg_c1

/-- info: 'ClayRiemannProof.Bicomplex.neg_c2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.neg_c2

/-- info: 'ClayRiemannProof.Bicomplex.sub_c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.sub_c1

/-- info: 'ClayRiemannProof.Bicomplex.sub_c2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.sub_c2

/-- info: 'ClayRiemannProof.Bicomplex.mul_c1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.mul_c1

/-- info: 'ClayRiemannProof.Bicomplex.mul_c2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.mul_c2

/-- info: 'ClayRiemannProof.Bicomplex.j' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.j

/-- info: 'ClayRiemannProof.Bicomplex.iBC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.iBC

/-- info: 'ClayRiemannProof.Bicomplex.k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.k

/-- info: 'ClayRiemannProof.Bicomplex.j_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.j_sq

/-- info: 'ClayRiemannProof.Bicomplex.i_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.i_sq

/-- info: 'ClayRiemannProof.Bicomplex.k_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.k_eq

/-- info: 'ClayRiemannProof.Bicomplex.k_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.k_sq

/-- info: 'ClayRiemannProof.Bicomplex.divisor_de_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.divisor_de_zero

/-- info: 'ClayRiemannProof.Bicomplex.plus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.plus

/-- info: 'ClayRiemannProof.Bicomplex.minus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.minus

/-- info: 'ClayRiemannProof.Bicomplex.plus_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.plus_add

/-- info: 'ClayRiemannProof.Bicomplex.minus_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.minus_add

/-- info: 'ClayRiemannProof.Bicomplex.plus_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.plus_mul

/-- info: 'ClayRiemannProof.Bicomplex.minus_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.minus_mul

/-- info: 'ClayRiemannProof.Bicomplex.ofPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.ofPair

/-- info: 'ClayRiemannProof.Bicomplex.plus_ofPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.plus_ofPair

/-- info: 'ClayRiemannProof.Bicomplex.minus_ofPair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.minus_ofPair

/-- info: 'ClayRiemannProof.Bicomplex.eq_iff_plus_minus' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.eq_iff_plus_minus

/-- info: 'ClayRiemannProof.Bicomplex.eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.eq_zero_iff

/-- info: 'ClayRiemannProof.Bicomplex.divisor_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.divisor_iff

/-- info: 'ClayRiemannProof.Bicomplex.zetaBC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.zetaBC

/-- info: 'ClayRiemannProof.Bicomplex.zetaBC_ofComplex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.zetaBC_ofComplex

/-- info: 'ClayRiemannProof.Bicomplex.zetaBC_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.zetaBC_eq_zero_iff

/-- info: 'ClayRiemannProof.Bicomplex.zetaBC_divisor_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.zetaBC_divisor_iff

/-- info: 'ClayRiemannProof.Bicomplex.NaoTrivial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.NaoTrivial

/-- info: 'ClayRiemannProof.Bicomplex.RHbc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.RHbc

/-- info: 'ClayRiemannProof.Bicomplex.target_iff_RHbc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.target_iff_RHbc

/-- info: 'ClayRiemannProof.Bicomplex.re_altura_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.re_altura_real

/-- info: 'ClayRiemannProof.Bicomplex.re_altura_complexa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bicomplex.re_altura_complexa

/-! ## `ClayRiemannProof/Locks.lean` -/

/-- info: 'ClayRiemannProof.Locks.target_iff_desvio_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Locks.target_iff_desvio_zero

/-- info: 'ClayRiemannProof.Locks.trava1_algebra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Locks.trava1_algebra

/-- info: 'ClayRiemannProof.Locks.ponte_vale_em_todo_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Locks.ponte_vale_em_todo_sigma

/-- info: 'ClayRiemannProof.Locks.ponte_em_sete_decimos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Locks.ponte_em_sete_decimos

/-- info: 'ClayRiemannProof.Locks.simetria_nao_basta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Locks.simetria_nao_basta

/-- info: 'ClayRiemannProof.Locks.trava2_complexo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Locks.trava2_complexo

/-- info: 'ClayRiemannProof.Locks.sem_divisor_de_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Locks.sem_divisor_de_zero

/-- info: 'ClayRiemannProof.Locks.zeta_tem_zeros_em_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Locks.zeta_tem_zeros_em_C

/-- info: 'ClayRiemannProof.Locks.euler_trava' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Locks.euler_trava

/-- info: 'ClayRiemannProof.Locks.retangulo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Locks.retangulo

/-- info: 'ClayRiemannProof.Bridges.delta_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.delta_injective

/-- info: 'ClayRiemannProof.Bridges.delta_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.delta_eq_zero_iff

/-- info: 'ClayRiemannProof.Bridges.delta_tensao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.delta_tensao

/-- info: 'ClayRiemannProof.Bridges.delta_espelho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.delta_espelho

/-- info: 'ClayRiemannProof.Bridges.delta_torcao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.delta_torcao

/-- info: 'ClayRiemannProof.Bridges.delta_compressao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.delta_compressao

/-- info: 'ClayRiemannProof.Bridges.baricentro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.baricentro

/-- info: 'ClayRiemannProof.Bridges.tensoes_cancelam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.tensoes_cancelam

/-- info: 'ClayRiemannProof.Bridges.energia_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.energia_eq

/-- info: 'ClayRiemannProof.Bridges.energia_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.energia_eq_zero_iff

/-- info: 'ClayRiemannProof.Bridges.energia_lt_um' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.energia_lt_um

/-- info: 'ClayRiemannProof.Bridges.vetor_de_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.vetor_de_zero

/-- info: 'ClayRiemannProof.Bridges.card_orbita_reta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.card_orbita_reta

/-- info: 'ClayRiemannProof.Bridges.card_orbita_fora' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.card_orbita_fora

/-- info: 'ClayRiemannProof.Bridges.target_iff_nos_desfeitos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.target_iff_nos_desfeitos

/-- info: 'ClayRiemannProof.Bridges.not_target_iff_no' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.not_target_iff_no

/-- info: 'ClayRiemannProof.Bridges.lam_tensao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.lam_tensao

/-- info: 'ClayRiemannProof.Bridges.lam_espelho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.lam_espelho

/-- info: 'ClayRiemannProof.Bridges.lam_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.lam_re

/-- info: 'ClayRiemannProof.Bridges.lam_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.lam_im

/-- info: 'ClayRiemannProof.Bridges.lam_na_reta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.lam_na_reta

/-- info: 'ClayRiemannProof.Bridges.target_iff_lam_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.target_iff_lam_real

/-- info: 'ClayRiemannProof.Bridges.lam_re_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.lam_re_gt

/-- info: 'ClayRiemannProof.Bridges.gam_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.gam_re

/-- info: 'ClayRiemannProof.Bridges.gam_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.gam_im

/-- info: 'ClayRiemannProof.Bridges.target_iff_gam_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.target_iff_gam_real

/-- info: 'ClayRiemannProof.Bridges.hilbert_polya' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.hilbert_polya

/-- info: 'ClayRiemannProof.Bridges.pontes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Bridges.pontes
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

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.mellinConvergent_rhoθ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.mellinConvergent_rhoθ

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.mellin_rhoθ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.mellin_rhoθ

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.fθ_eq_zero_of_one_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.fθ_eq_zero_of_one_lt

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.fθ_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.fθ_eq

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.mellinConvergent_fθ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.mellinConvergent_fθ

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.mellin_fθ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.mellin_fθ

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.mellin_fθ_eq_integral_Ioc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.mellin_fθ_eq_integral_Ioc

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.integral_Ioc_fθ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.integral_Ioc_fθ

/-- info: 'ClayRiemannProof.BaezDuarte.NymanBeurling.integral_Ioc_fθ_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BaezDuarte.NymanBeurling.integral_Ioc_fθ_eq_zero

/-! ## `ClayRiemannProof/TresTravas.lean` -/

/-- info: 'ClayRiemannProof.TresTravas.Travas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.TresTravas.Travas

/-- info: 'ClayRiemannProof.TresTravas.zeta_tem_as_tres' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.TresTravas.zeta_tem_as_tres

/-- info: 'ClayRiemannProof.TresTravas.quarteto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.TresTravas.quarteto

/-- info: 'ClayRiemannProof.TresTravas.G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.TresTravas.G

/-- info: 'ClayRiemannProof.TresTravas.G_inteira' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.TresTravas.G_inteira

/-- info: 'ClayRiemannProof.TresTravas.G_ponte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.TresTravas.G_ponte

/-- info: 'ClayRiemannProof.TresTravas.G_conjugacao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.TresTravas.G_conjugacao

/-- info: 'ClayRiemannProof.TresTravas.fator_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.TresTravas.fator_ne_zero

/-- info: 'ClayRiemannProof.TresTravas.G_euler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.TresTravas.G_euler

/-- info: 'ClayRiemannProof.TresTravas.G_travas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.TresTravas.G_travas

/-- info: 'ClayRiemannProof.TresTravas.G_zero_quarto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.TresTravas.G_zero_quarto

/-- info: 'ClayRiemannProof.TresTravas.G_zero_tres_quartos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.TresTravas.G_zero_tres_quartos

/-- info: 'ClayRiemannProof.TresTravas.tres_travas_nao_bastam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.TresTravas.tres_travas_nao_bastam

/-- info: 'ClayRiemannProof.TresTravas.retangulo_nao_colapsa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.TresTravas.retangulo_nao_colapsa

/-- info: 'ClayRiemannProof.TresTravas.sem_ponte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.TresTravas.sem_ponte

/-- info: 'ClayRiemannProof.TresTravas.E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.TresTravas.E

/-- info: 'ClayRiemannProof.TresTravas.sem_euler' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.TresTravas.sem_euler

/-- info: 'ClayRiemannProof.TresTravas.C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.TresTravas.C

/-- info: 'ClayRiemannProof.TresTravas.sem_conjugacao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.TresTravas.sem_conjugacao

/-- info: 'ClayRiemannProof.TresTravas.travas_independentes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.TresTravas.travas_independentes


/-- info: 'ClayRiemannProof.Analogs.quarteto_abstrato' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Analogs.quarteto_abstrato

/-- info: 'ClayRiemannProof.Analogs.xi_simetrica' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Analogs.xi_simetrica

/-- info: 'ClayRiemannProof.Analogs.quartetoPoly_simetrica' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Analogs.quartetoPoly_simetrica

/-- info: 'ClayRiemannProof.Analogs.simetria_nao_basta_abstrata' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Analogs.simetria_nao_basta_abstrata

/-- info: 'ClayRiemannProof.Analogs.partes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Analogs.partes

/-- info: 'ClayRiemannProof.Analogs.ihara_ramanujan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Analogs.ihara_ramanujan

/-- info: 'ClayRiemannProof.Analogs.ihara_fora_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Analogs.ihara_fora_real

/-- info: 'ClayRiemannProof.Analogs.ihara_quarteto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Analogs.ihara_quarteto

/-- info: 'ClayRiemannProof.Analogs.circulo_iff_reta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Analogs.circulo_iff_reta

/-- info: 'ClayRiemannProof.Analogs.lee_yang_dois_spins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Analogs.lee_yang_dois_spins

/-- info: 'ClayRiemannProof.Analogs.lee_yang_ferro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Analogs.lee_yang_ferro

/-- info: 'ClayRiemannProof.Analogs.lam_real_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Analogs.lam_real_iff

/-- info: 'ClayRiemannProof.Analogs.linha_iff_quarto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Analogs.linha_iff_quarto

/-- info: 'ClayRiemannProof.Analogs.excepcional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Analogs.excepcional

/-- info: 'ClayRiemannProof.Analogs.zeta_sem_saida_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Analogs.zeta_sem_saida_real

/-- info: 'ClayRiemannProof.Analogs.selberg_polya' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Analogs.selberg_polya

/-! ## `ClayRiemannProof/Fronteira/Hadamard.lean` -/

/-- info: 'ClayRiemannProof.Fronteira.xi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fronteira.xi

/-- info: 'ClayRiemannProof.Fronteira.xi_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fronteira.xi_one_sub

/-- info: 'ClayRiemannProof.Fronteira.differentiable_xi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fronteira.differentiable_xi

/-- info: 'ClayRiemannProof.Fronteira.xi_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fronteira.xi_zero

/-- info: 'ClayRiemannProof.Fronteira.xi_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fronteira.xi_one

/-- info: 'ClayRiemannProof.Fronteira.xi_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fronteira.xi_eq

/-- info: 'ClayRiemannProof.Fronteira.XiHadamard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fronteira.XiHadamard


/-! ## `ClayRiemannProof/Fronteira/Li.lean` -/

/-- info: 'ClayRiemannProof.Fronteira.liCoeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fronteira.liCoeff

/-- info: 'ClayRiemannProof.Fronteira.CriterioDeLi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fronteira.CriterioDeLi

/-- info: 'ClayRiemannProof.Fronteira.PositividadeDeLi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fronteira.PositividadeDeLi


/-! ## `ClayRiemannProof/Fronteira/Ht.lean` -/

/-- info: 'ClayRiemannProof.Fronteira.Phi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fronteira.Phi

/-- info: 'ClayRiemannProof.Fronteira.H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fronteira.H

/-- info: 'ClayRiemannProof.Fronteira.deBruijnNewman' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fronteira.deBruijnNewman

/-- info: 'ClayRiemannProof.Fronteira.H0_eh_xi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fronteira.H0_eh_xi

/-- info: 'ClayRiemannProof.Fronteira.RodgersTao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fronteira.RodgersTao

/-- info: 'ClayRiemannProof.Fronteira.RH_iff_Lambda' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fronteira.RH_iff_Lambda

/-- info: 'ClayRiemannProof.Fronteira.PlattTrudgianLambda' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fronteira.PlattTrudgianLambda


/-! ## `ClayRiemannProof/Fronteira/Clay.lean` -/

/-- info: 'ClayRiemannProof.Fronteira.clay_como_proposto_falso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fronteira.clay_como_proposto_falso

/-- info: 'ClayRiemannProof.Fronteira.target_de_li' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fronteira.target_de_li

/-- info: 'ClayRiemannProof.Fronteira.target_de_dbn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Fronteira.target_de_dbn

/-- info: 'ClayRiemannProof.Xi.differentiable_xi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Xi.differentiable_xi

/-- info: 'ClayRiemannProof.Xi.xi_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Xi.xi_eq

/-- info: 'ClayRiemannProof.Xi.xi_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Xi.xi_zero

/-- info: 'ClayRiemannProof.Xi.xi_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Xi.xi_one

/-- info: 'ClayRiemannProof.Xi.xi_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Xi.xi_one_sub

/-- info: 'ClayRiemannProof.Xi.xi_conj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Xi.xi_conj

/-- info: 'ClayRiemannProof.Xi.completed_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Xi.completed_eq_zero_iff

/-- info: 'ClayRiemannProof.Xi.xi_ne_zero_of_one_le_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Xi.xi_ne_zero_of_one_le_re

/-- info: 'ClayRiemannProof.Xi.xi_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Xi.xi_eq_zero_iff

/-- info: 'ClayRiemannProof.Xi.target_iff_xi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Xi.target_iff_xi

/-- info: 'ClayRiemannProof.Xi.esqueleto_falso' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Xi.esqueleto_falso

/-- info: 'ClayRiemannProof.Xi.hasDerivAt_xi_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Xi.hasDerivAt_xi_one

/-- info: 'ClayRiemannProof.Xi.li_one_eq_logDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Xi.li_one_eq_logDeriv

/-- info: 'ClayRiemannProof.Xi.li_one_eq_completed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Xi.li_one_eq_completed

/-- info: 'ClayRiemannProof.Xi.li_one_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Xi.li_one_eq

/-- info: 'ClayRiemannProof.Xi.gamma_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Xi.gamma_gt

/-- info: 'ClayRiemannProof.Xi.log_four_pi_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Xi.log_four_pi_lt

/-- info: 'ClayRiemannProof.Xi.log_four_pi_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Xi.log_four_pi_gt

/-- info: 'ClayRiemannProof.Xi.li_one_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Xi.li_one_bounds

/-- info: 'ClayRiemannProof.Xi.li_one_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Xi.li_one_pos

/-- info: 'ClayRiemannProof.LiCircle.mob_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.mob_eq

/-- info: 'ClayRiemannProof.LiCircle.mob_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.mob_ne_zero

/-- info: 'ClayRiemannProof.LiCircle.normSq_sub_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.normSq_sub_one_sub

/-- info: 'ClayRiemannProof.LiCircle.normSq_mob_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.normSq_mob_eq_one_iff

/-- info: 'ClayRiemannProof.LiCircle.normSq_mob_lt_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.normSq_mob_lt_one_iff

/-- info: 'ClayRiemannProof.LiCircle.norm_eq_one_iff_normSq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.norm_eq_one_iff_normSq

/-- info: 'ClayRiemannProof.LiCircle.mob_espelho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.mob_espelho

/-- info: 'ClayRiemannProof.LiCircle.mob_tensao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.mob_tensao

/-- info: 'ClayRiemannProof.LiCircle.mob_torcao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.mob_torcao

/-- info: 'ClayRiemannProof.LiCircle.liQ_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.liQ_eq

/-- info: 'ClayRiemannProof.LiCircle.liQ_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.liQ_inv

/-- info: 'ClayRiemannProof.LiCircle.re_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.re_pow

/-- info: 'ClayRiemannProof.LiCircle.exists_re_pow_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.exists_re_pow_gt

/-- info: 'ClayRiemannProof.LiCircle.liQ_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.liQ_neg

/-- info: 'ClayRiemannProof.LiCircle.li_quarteto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.li_quarteto

/-- info: 'ClayRiemannProof.LiCircle.liQ_mob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.liQ_mob

/-- info: 'ClayRiemannProof.LiCircle.li_termo_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.li_termo_nonneg

/-- info: 'ClayRiemannProof.LiCircle.ne_zero_of_mem_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.ne_zero_of_mem_Z

/-- info: 'ClayRiemannProof.LiCircle.ne_one_of_mem_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.ne_one_of_mem_Z

/-- info: 'ClayRiemannProof.LiCircle.target_iff_circulo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.target_iff_circulo

/-- info: 'ClayRiemannProof.LiCircle.target_iff_li_quartetos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.target_iff_li_quartetos

/-- info: 'ClayRiemannProof.LiCircle.target_iff_ramanujan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.target_iff_ramanujan

/-- info: 'ClayRiemannProof.LiCircle.encontro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiCircle.encontro

/-- info: 'ClayRiemannProof.LiFinite.cayley_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiFinite.cayley_mul

/-- info: 'ClayRiemannProof.LiFinite.normSq_cayley_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiFinite.normSq_cayley_mul

/-- info: 'ClayRiemannProof.LiFinite.norm_sq_cayley' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiFinite.norm_sq_cayley

/-- info: 'ClayRiemannProof.LiFinite.norm_cayley_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiFinite.norm_cayley_eq_one_iff

/-- info: 'ClayRiemannProof.LiFinite.one_lt_norm_cayley_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiFinite.one_lt_norm_cayley_iff

/-- info: 'ClayRiemannProof.LiFinite.bnd_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiFinite.bnd_nonneg

/-- info: 'ClayRiemannProof.LiFinite.re_geom_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiFinite.re_geom_ge

/-- info: 'ClayRiemannProof.LiFinite.re_mul_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiFinite.re_mul_re

/-- info: 'ClayRiemannProof.LiFinite.li_chave' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiFinite.li_chave

/-- info: 'ClayRiemannProof.LiFinite.li_finito' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiFinite.li_finito

/-- info: 'ClayRiemannProof.LiFinite.li_no_mundo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiFinite.li_no_mundo

/-- info: 'ClayRiemannProof.LiFinite.li_detecta_fora_da_reta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LiFinite.li_detecta_fora_da_reta

/-- info: 'ClayRiemannProof.Turing.naReta_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Turing.naReta_re

/-- info: 'ClayRiemannProof.Turing.naReta_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Turing.naReta_im

/-- info: 'ClayRiemannProof.Turing.naReta_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Turing.naReta_injective

/-- info: 'ClayRiemannProof.Turing.naReta_mem_Z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Turing.naReta_mem_Z

/-- info: 'ClayRiemannProof.Turing.zero_em_aberto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Turing.zero_em_aberto

/-- info: 'ClayRiemannProof.Turing.trocas_de_sinal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Turing.trocas_de_sinal

/-- info: 'ClayRiemannProof.Turing.turing_logica' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Turing.turing_logica

/-- info: 'ClayRiemannProof.Turing.turing_janela' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Turing.turing_janela

/-- info: 'ClayRiemannProof.Turing.janelas_colam' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Turing.janelas_colam

/-- info: 'ClayRiemannProof.Turing.rhateZ_estende' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Turing.rhateZ_estende

/-- info: 'ClayRiemannProof.Turing.rhNoMundo_estende' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Turing.rhNoMundo_estende

/-! ## `ClayRiemannProof/Colisao.lean` -/

/-- info: 'ClayRiemannProof.Colisao.H2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Colisao.H2

/-- info: 'ClayRiemannProof.Colisao.calor_t' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Colisao.calor_t

/-- info: 'ClayRiemannProof.Colisao.calor_z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Colisao.calor_z

/-- info: 'ClayRiemannProof.Colisao.zeros_reais_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Colisao.zeros_reais_iff

/-- info: 'ClayRiemannProof.Colisao.colisao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Colisao.colisao

/-- info: 'ClayRiemannProof.Colisao.mais_proximo_sai_depois' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Colisao.mais_proximo_sai_depois

/-- info: 'ClayRiemannProof.Colisao.na_reta_em_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Colisao.na_reta_em_zero

/-- info: 'ClayRiemannProof.Colisao.raiz_quadrada' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Colisao.raiz_quadrada

/-- info: 'ClayRiemannProof.Verification.injetiva_de_derivada' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Verification.injetiva_de_derivada

/-- info: 'ClayRiemannProof.Verification.norm_torcao_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Verification.norm_torcao_sub

/-- info: 'ClayRiemannProof.Verification.torcao_mem_ball' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Verification.torcao_mem_ball

/-- info: 'ClayRiemannProof.Verification.zero_na_bola_simetrica' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Verification.zero_na_bola_simetrica

/-- info: 'ClayRiemannProof.Verification.zero_unico_na_bola' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Verification.zero_unico_na_bola

/-- info: 'ClayRiemannProof.Verification.janelaNaReta_de_bolas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Verification.janelaNaReta_de_bolas

/-- info: 'ClayRiemannProof.Verification.rhAteZ_de_bolas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Verification.rhAteZ_de_bolas

/-- info: 'ClayRiemannProof.Verification.logDeriv_completada' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Verification.logDeriv_completada

/-! ## `ClayRiemannProof/PrimeiroFora.lean` -/

/-- info: 'ClayRiemannProof.PrimeiroFora.preconexo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.PrimeiroFora.preconexo

/-- info: 'ClayRiemannProof.PrimeiroFora.analitica' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.PrimeiroFora.analitica

/-- info: 'ClayRiemannProof.PrimeiroFora.zeros_isolados' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.PrimeiroFora.zeros_isolados

/-- info: 'ClayRiemannProof.PrimeiroFora.zeros_finitos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.PrimeiroFora.zeros_finitos

/-- info: 'ClayRiemannProof.PrimeiroFora.im_gt_13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.PrimeiroFora.im_gt_13

/-- info: 'ClayRiemannProof.PrimeiroFora.representante' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.PrimeiroFora.representante

/-- info: 'ClayRiemannProof.PrimeiroFora.primeiro_fora' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.PrimeiroFora.primeiro_fora

/-- info: 'ClayRiemannProof.PrimeiroFora.primeiro_fora_acima' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.PrimeiroFora.primeiro_fora_acima

/-- info: 'ClayRiemannProof.PrimeiroFora.primeiro_fora_acima_13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.PrimeiroFora.primeiro_fora_acima_13

/-- info: 'ClayRiemannProof.PrimeiroFora.rhAteZ_janela' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.PrimeiroFora.rhAteZ_janela

/-- info: 'ClayRiemannProof.PrimeiroFora.primeiro_fora_acima_janela' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.PrimeiroFora.primeiro_fora_acima_janela

/-! ## `ClayRiemannProof/PontesTotal.lean` -/

/-- info: 'ClayRiemannProof.PontesTotal.pontes_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.PontesTotal.pontes_total

/-! ## `ClayRiemannProof/BicomplexConditional.lean` -/

/-- info: 'ClayRiemannProof.BicomplexConditional.both_components_RH_force_center' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexConditional.both_components_RH_force_center

/-- info: 'ClayRiemannProof.BicomplexConditional.one_component_does_not_force_b_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexConditional.one_component_does_not_force_b_zero

/-- info: 'ClayRiemannProof.BicomplexConditional.component_coordinates_force_center' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexConditional.component_coordinates_force_center

/-! ## `ClayRiemannProof/CenteredStabilityBridge.lean` -/

/-- info: 'ClayRiemannProof.CenteredStabilityBridge.re_centered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CenteredStabilityBridge.re_centered

/-- info: 'ClayRiemannProof.CenteredStabilityBridge.centered_on_axis_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CenteredStabilityBridge.centered_on_axis_iff

/-- info: 'ClayRiemannProof.CenteredStabilityBridge.centered_reflection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CenteredStabilityBridge.centered_reflection

/-- info: 'ClayRiemannProof.CenteredStabilityBridge.riemann_iff_centered_neutral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CenteredStabilityBridge.riemann_iff_centered_neutral

/-- info: 'ClayRiemannProof.CenteredStabilityBridge.hypothetical_rectangle_real_parts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CenteredStabilityBridge.hypothetical_rectangle_real_parts

/-! ## `ClayRiemannProof/BicomplexCoordinates.lean` -/

/-- info: 'ClayRiemannProof.BicomplexCoordinates.re_verticalPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.re_verticalPoint

/-- info: 'ClayRiemannProof.BicomplexCoordinates.re_verticalPoint_eq_of_same_sigma' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.re_verticalPoint_eq_of_same_sigma

/-- info: 'ClayRiemannProof.BicomplexCoordinates.critical_coordinate_eq_half' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.critical_coordinate_eq_half

/-- info: 'ClayRiemannProof.BicomplexCoordinates.neg_half_of_critical_coordinate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.neg_half_of_critical_coordinate

/-- info: 'ClayRiemannProof.BicomplexCoordinates.i_sq' does not depend on any axioms -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.i_sq

/-- info: 'ClayRiemannProof.BicomplexCoordinates.j_sq' does not depend on any axioms -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.j_sq

/-- info: 'ClayRiemannProof.BicomplexCoordinates.ij_eq_k' does not depend on any axioms -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.ij_eq_k

/-- info: 'ClayRiemannProof.BicomplexCoordinates.ji_eq_k' does not depend on any axioms -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.ji_eq_k

/-- info: 'ClayRiemannProof.BicomplexCoordinates.k_sq' does not depend on any axioms -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.k_sq

/-- info: 'ClayRiemannProof.BicomplexCoordinates.j_inverse_left' does not depend on any axioms -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.j_inverse_left

/-- info: 'ClayRiemannProof.BicomplexCoordinates.j_inverse_right' does not depend on any axioms -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.j_inverse_right

/-- info: 'ClayRiemannProof.BicomplexCoordinates.j_ne_i' does not depend on any axioms -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.j_ne_i

/-- info: 'ClayRiemannProof.BicomplexCoordinates.j_ne_neg_i' does not depend on any axioms -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.j_ne_neg_i

/-- info: 'ClayRiemannProof.BicomplexCoordinates.real_of_negative_one_ne_two' does not depend on any axioms -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.real_of_negative_one_ne_two

/-- info: 'ClayRiemannProof.BicomplexCoordinates.j_coordinate_norm_sq' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.j_coordinate_norm_sq

/-- info: 'ClayRiemannProof.BicomplexCoordinates.idempotent_zero_divisors' does not depend on any axioms -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.idempotent_zero_divisors

/-- info: 'ClayRiemannProof.BicomplexCoordinates.one_add_k_ne_zero' does not depend on any axioms -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.one_add_k_ne_zero

/-- info: 'ClayRiemannProof.BicomplexCoordinates.one_sub_k_ne_zero' does not depend on any axioms -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.one_sub_k_ne_zero

/-- info: 'ClayRiemannProof.BicomplexCoordinates.i_mul_complex' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.i_mul_complex

/-- info: 'ClayRiemannProof.BicomplexCoordinates.i_mul_second_plane' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.i_mul_second_plane

/-- info: 'ClayRiemannProof.BicomplexCoordinates.real_minus_one_plus_i_complex_y' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.real_minus_one_plus_i_complex_y

/-- info: 'ClayRiemannProof.BicomplexCoordinates.real_minus_one_plus_i_real_y' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.real_minus_one_plus_i_real_y

/-- info: 'ClayRiemannProof.BicomplexCoordinates.real_minus_one_plus_i_independent_j' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.real_minus_one_plus_i_independent_j

/-- info: 'ClayRiemannProof.BicomplexCoordinates.complex_y_example_re_two' does not depend on any axioms -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.complex_y_example_re_two

/-- info: 'ClayRiemannProof.BicomplexCoordinates.complex_y_example_zero' does not depend on any axioms -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.complex_y_example_zero

/-- info: 'ClayRiemannProof.BicomplexCoordinates.projection_b_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayRiemannProof.BicomplexCoordinates.projection_b_zero
/-! ## `ClayRiemannProof/QuartetoForcado.lean` -/

/-- info: 'ClayRiemannProof.QuartetoForcado.Q' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.QuartetoForcado.Q

/-- info: 'ClayRiemannProof.QuartetoForcado.Q_simetrica' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.QuartetoForcado.Q_simetrica

/-- info: 'ClayRiemannProof.QuartetoForcado.quadrado_neg_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.QuartetoForcado.quadrado_neg_re

/-- info: 'ClayRiemannProof.QuartetoForcado.Q_na_reta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.QuartetoForcado.Q_na_reta

/-- info: 'ClayRiemannProof.QuartetoForcado.Q_quarteto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.QuartetoForcado.Q_quarteto

/-- info: 'ClayRiemannProof.QuartetoForcado.quarteto_forcado' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.QuartetoForcado.quarteto_forcado

/-- info: 'ClayRiemannProof.QuartetoForcado.Q_quarteto_abstrato' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.QuartetoForcado.Q_quarteto_abstrato

/-! ## `ClayRiemannProof/Lehmer.lean` -/

/-- info: 'ClayRiemannProof.Lehmer.csv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Lehmer.csv

/-- info: 'ClayRiemannProof.Lehmer.bernoulli_quatro_quintos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Lehmer.bernoulli_quatro_quintos

/-- info: 'ClayRiemannProof.Lehmer.acima_da_reta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Lehmer.acima_da_reta

/-- info: 'ClayRiemannProof.Lehmer.csv_le_isolado' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Lehmer.csv_le_isolado

/-- info: 'ClayRiemannProof.Lehmer.csv_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Lehmer.csv_ge

/-- info: 'ClayRiemannProof.Lehmer.csv_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Lehmer.csv_neg

/-- info: 'ClayRiemannProof.Lehmer.csv_escala' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Lehmer.csv_escala

/-- info: 'ClayRiemannProof.Lehmer.csv_x_de_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Lehmer.csv_x_de_gamma

/-- info: 'ClayRiemannProof.Lehmer.csv_limite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Lehmer.csv_limite

/-- info: 'ClayRiemannProof.Lehmer.dif_bolas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Lehmer.dif_bolas

/-- info: 'ClayRiemannProof.Lehmer.csv_por_distancia' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Lehmer.csv_por_distancia

/-- info: 'ClayRiemannProof.Lehmer.aglomerado_052_053' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Lehmer.aglomerado_052_053

/-- info: 'ClayRiemannProof.Lehmer.par_mais_fragil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Lehmer.par_mais_fragil

/-! ## `ClayRiemannProof/Paridade.lean` -/

/-- info: 'ClayRiemannProof.Paridade.card_par_aux' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Paridade.card_par_aux

/-- info: 'ClayRiemannProof.Paridade.NaJanela' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Paridade.NaJanela

/-- info: 'ClayRiemannProof.Paridade.NaReta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Paridade.NaReta

/-- info: 'ClayRiemannProof.Paridade.Fora' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Paridade.Fora

/-- info: 'ClayRiemannProof.Paridade.naJanela_finita' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Paridade.naJanela_finita

/-- info: 'ClayRiemannProof.Paridade.fora_finito' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Paridade.fora_finito

/-- info: 'ClayRiemannProof.Paridade.naReta_finita' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Paridade.naReta_finita

/-- info: 'ClayRiemannProof.Paridade.im_torcao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Paridade.im_torcao

/-- info: 'ClayRiemannProof.Paridade.torcao_fora' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Paridade.torcao_fora

/-- info: 'ClayRiemannProof.Paridade.torcao_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Paridade.torcao_ne

/-- info: 'ClayRiemannProof.Paridade.fora_par' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Paridade.fora_par

/-- info: 'ClayRiemannProof.Paridade.janela_uniao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Paridade.janela_uniao

/-- info: 'ClayRiemannProof.Paridade.contagem_soma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Paridade.contagem_soma

/-- info: 'ClayRiemannProof.Paridade.furo_de_dois' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Paridade.furo_de_dois

/-- info: 'ClayRiemannProof.Paridade.contagem_fecha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Paridade.contagem_fecha

/-- info: 'ClayRiemannProof.Paridade.fecha_de_contagens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Paridade.fecha_de_contagens

/-- info: 'ClayRiemannProof.Paridade.no_aglomerado_sem_fora' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Paridade.no_aglomerado_sem_fora

/-! ## `ClayRiemannProof/Gram.lean` -/

/-- info: 'ClayRiemannProof.Gram.S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Gram.S

/-- info: 'ClayRiemannProof.Gram.S_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Gram.S_gram

/-- info: 'ClayRiemannProof.Gram.S_gram_inteiro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Gram.S_gram_inteiro

/-- info: 'ClayRiemannProof.Gram.zeros_no_bloco' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Gram.zeros_no_bloco

/-- info: 'ClayRiemannProof.Gram.Bom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Gram.Bom

/-- info: 'ClayRiemannProof.Gram.bloco_par' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Gram.bloco_par

/-- info: 'ClayRiemannProof.Gram.aglomerado_rosser' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Gram.aglomerado_rosser

/-! ## `ClayRiemannProof/QuartetoDesenhado.lean` -/

/-- info: 'ClayRiemannProof.QuartetoDesenhado.cota_07_mais' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.QuartetoDesenhado.cota_07_mais

/-- info: 'ClayRiemannProof.QuartetoDesenhado.cota_03_mais' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.QuartetoDesenhado.cota_03_mais

/-- info: 'ClayRiemannProof.QuartetoDesenhado.cota_07_menos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.QuartetoDesenhado.cota_07_menos

/-- info: 'ClayRiemannProof.QuartetoDesenhado.cota_03_menos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.QuartetoDesenhado.cota_03_menos

/-- info: 'ClayRiemannProof.QuartetoDesenhado.nao_zero_de_cota' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.QuartetoDesenhado.nao_zero_de_cota

/-- info: 'ClayRiemannProof.QuartetoDesenhado.quarteto_desenhado' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.QuartetoDesenhado.quarteto_desenhado

/-! ## `ClayRiemannProof/Continuacao.lean` -/

/-- info: 'ClayRiemannProof.Continuacao.JanelaContinuacao2026' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Continuacao.JanelaContinuacao2026

/-- info: 'ClayRiemannProof.Continuacao.rhAteZ_continuacao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Continuacao.rhAteZ_continuacao

/-- info: 'ClayRiemannProof.Continuacao.primeiro_fora_acima_continuacao' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Continuacao.primeiro_fora_acima_continuacao

/-- info: 'ClayRiemannProof.Continuacao.par_mais_fragil_continuacao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Continuacao.par_mais_fragil_continuacao

/-- info: 'ClayRiemannProof.Continuacao.par_mais_fragil_1e18' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Continuacao.par_mais_fragil_1e18

/-- info: 'ClayRiemannProof.Continuacao.par_mais_fragil_onda2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Continuacao.par_mais_fragil_onda2

/-- info: 'ClayRiemannProof.Continuacao.par_mais_fragil_onda_1e14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Continuacao.par_mais_fragil_onda_1e14

/-- info: 'ClayRiemannProof.Continuacao.JanelaContinuacao2026b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Continuacao.JanelaContinuacao2026b

/-- info: 'ClayRiemannProof.Continuacao.rhAteZ_continuacao2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Continuacao.rhAteZ_continuacao2

/-- info: 'ClayRiemannProof.Continuacao.primeiro_fora_acima_continuacao2' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Continuacao.primeiro_fora_acima_continuacao2

/-- info: 'ClayRiemannProof.Continuacao.par_mais_fragil_continuacao2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Continuacao.par_mais_fragil_continuacao2

/-- info: 'ClayRiemannProof.Continuacao.JanelaContinuacao2026c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Continuacao.JanelaContinuacao2026c

/-- info: 'ClayRiemannProof.Continuacao.rhAteZ_continuacao3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Continuacao.rhAteZ_continuacao3

/-- info: 'ClayRiemannProof.Continuacao.primeiro_fora_acima_continuacao3' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Continuacao.primeiro_fora_acima_continuacao3

/-- info: 'ClayRiemannProof.Continuacao.par_mais_fragil_continuacao3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Continuacao.par_mais_fragil_continuacao3

/-- info: 'ClayRiemannProof.Continuacao.rhAteZ_continuacao4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Continuacao.rhAteZ_continuacao4

/-- info: 'ClayRiemannProof.Continuacao.primeiro_fora_acima_continuacao4' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Continuacao.primeiro_fora_acima_continuacao4

/-- info: 'ClayRiemannProof.Continuacao.par_mais_fragil_continuacao4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Continuacao.par_mais_fragil_continuacao4

/-! ## `ClayRiemannProof/Absorcao.lean` -/

/-- info: 'ClayRiemannProof.Absorcao.media_reAbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.media_reAbs

/-- info: 'ClayRiemannProof.Absorcao.media_normalizada_um' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.media_normalizada_um

/-- info: 'ClayRiemannProof.Absorcao.reAbs_eq_meio_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.reAbs_eq_meio_iff

/-- info: 'ClayRiemannProof.Absorcao.media_meio_sem_ponto_meio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.media_meio_sem_ponto_meio

/-- info: 'ClayRiemannProof.Absorcao.fracoes_do_texto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.fracoes_do_texto

/-- info: 'ClayRiemannProof.Absorcao.cauda_longa_b_pequeno' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.cauda_longa_b_pequeno

/-- info: 'ClayRiemannProof.Absorcao.theta_media_contraexemplo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.theta_media_contraexemplo

/-- info: 'ClayRiemannProof.Absorcao.theta_le_tangente' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.theta_le_tangente

/-- info: 'ClayRiemannProof.Absorcao.theta_lt_tangente' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.theta_lt_tangente

/-- info: 'ClayRiemannProof.Absorcao.media_theta_negativa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.media_theta_negativa

/-- info: 'ClayRiemannProof.Absorcao.soma_primos_sse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.soma_primos_sse

/-- info: 'ClayRiemannProof.Absorcao.soma_quadrados_primos_sse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.soma_quadrados_primos_sse

/-- info: 'ClayRiemannProof.Absorcao.tcol_coordenadas' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.tcol_coordenadas

/-- info: 'ClayRiemannProof.Absorcao.tcol_do_texto_fora_do_intervalo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.tcol_do_texto_fora_do_intervalo

/-- info: 'ClayRiemannProof.Absorcao.gbar_nao_exato' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.gbar_nao_exato

/-- info: 'ClayRiemannProof.Absorcao.erro_bola_relativo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.erro_bola_relativo

/-- info: 'ClayRiemannProof.Absorcao.theta_estrita_crescente' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.theta_estrita_crescente

/-- info: 'ClayRiemannProof.Absorcao.euler_em_meio_diverge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.euler_em_meio_diverge

/-- info: 'ClayRiemannProof.Absorcao.inv_raiz_primo_irracional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.inv_raiz_primo_irracional

/-- info: 'ClayRiemannProof.Absorcao.inv_raiz_dois_sem_fracao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.inv_raiz_dois_sem_fracao

/-- info: 'ClayRiemannProof.Absorcao.desvio_eh_da_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.desvio_eh_da_formula

/-- info: 'ClayRiemannProof.Absorcao.tcol_s_arredondado_fora' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.tcol_s_arredondado_fora

/-- info: 'ClayRiemannProof.Absorcao.tcol_lacuna_medida_dentro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Absorcao.tcol_lacuna_medida_dentro

/-! ## `ClayRiemannProof/Alturas.lean` -/

/-- info: 'ClayRiemannProof.Alturas.par_mais_fragil_1e14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Alturas.par_mais_fragil_1e14

/-- info: 'ClayRiemannProof.Alturas.par_mais_fragil_1e16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Alturas.par_mais_fragil_1e16

/-- info: 'ClayRiemannProof.Alturas.par_mais_fragil_1e17' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Alturas.par_mais_fragil_1e17

/-! ## `ClayRiemannProof/Forca.lean` -/

/-- info: 'ClayRiemannProof.Forca.lombada' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Forca.lombada

/-- info: 'ClayRiemannProof.Forca.im_eq_zero_of_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Forca.im_eq_zero_of_sq

/-- info: 'ClayRiemannProof.Forca.lombada_reais_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Forca.lombada_reais_iff

/-- info: 'ClayRiemannProof.Forca.par_fora_da_reta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Forca.par_fora_da_reta

/-- info: 'ClayRiemannProof.Forca.lombada_do_par' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Forca.lombada_do_par

/-- info: 'ClayRiemannProof.Forca.limiar_do_par' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Forca.limiar_do_par

/-- info: 'ClayRiemannProof.Forca.calor_eh_empurrao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Forca.calor_eh_empurrao

/-- info: 'ClayRiemannProof.Forca.menos_forca' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Forca.menos_forca

/-- info: 'ClayRiemannProof.Forca.empurrao_simetrico' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Forca.empurrao_simetrico

/-- info: 'ClayRiemannProof.Forca.constante_simetrica' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Forca.constante_simetrica

/-- info: 'ClayRiemannProof.Forca.zeta_empurrada_quarteto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Forca.zeta_empurrada_quarteto

/-! ## `ClayRiemannProof/Empurrao.lean` -/

/-- info: 'ClayRiemannProof.Empurrao.fora' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Empurrao.fora

/-- info: 'ClayRiemannProof.Empurrao.fora_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Empurrao.fora_mono

/-- info: 'ClayRiemannProof.Empurrao.fora_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Empurrao.fora_eq_zero_iff

/-- info: 'ClayRiemannProof.Empurrao.limiar_da_janela' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Empurrao.limiar_da_janela

/-- info: 'ClayRiemannProof.Empurrao.fora_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Empurrao.fora_total

/-- info: 'ClayRiemannProof.Empurrao.fora_uniao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Empurrao.fora_uniao

/-- info: 'ClayRiemannProof.Empurrao.fora_composta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Empurrao.fora_composta

/-- info: 'ClayRiemannProof.Empurrao.minimo_desce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Empurrao.minimo_desce

/-- info: 'ClayRiemannProof.Empurrao.empurrao_fixo_acaba_tirando' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Empurrao.empurrao_fixo_acaba_tirando
/-! ## `ClayRiemannProof/Leis.lean` -/

/-- info: 'ClayRiemannProof.Leis.card_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.card_split

/-- info: 'ClayRiemannProof.Leis.lei_mestra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.lei_mestra

/-- info: 'ClayRiemannProof.Leis.lei_vazio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.lei_vazio

/-- info: 'ClayRiemannProof.Leis.S_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.S_gram

/-- info: 'ClayRiemannProof.Leis.lei_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.lei_gram

/-- info: 'ClayRiemannProof.Leis.vazio_gram' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.vazio_gram

/-- info: 'ClayRiemannProof.Leis.gram_triplo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.gram_triplo

/-- info: 'ClayRiemannProof.Leis.rosser_bloco' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.rosser_bloco

/-- info: 'ClayRiemannProof.Leis.aglomerado_e_vazio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.aglomerado_e_vazio

/-- info: 'ClayRiemannProof.Leis.re_s_de_z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.re_s_de_z

/-- info: 'ClayRiemannProof.Leis.im_s_de_z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.im_s_de_z

/-- info: 'ClayRiemannProof.Leis.colisao_em_gama' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.colisao_em_gama

/-- info: 'ClayRiemannProof.Leis.colisao_em_gama'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.colisao_em_gama'

/-- info: 'ClayRiemannProof.Leis.colisao_par_mais_fragil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.colisao_par_mais_fragil

/-- info: 'ClayRiemannProof.Leis.sem_deslocamento' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.sem_deslocamento

/-- info: 'ClayRiemannProof.Leis.sem_deslocamento_em_2e5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.sem_deslocamento_em_2e5

/-- info: 'ClayRiemannProof.Leis.deslocamento_forcado' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.deslocamento_forcado

/-- info: 'ClayRiemannProof.Leis.vec_tensao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.vec_tensao

/-- info: 'ClayRiemannProof.Leis.vec_espelho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.vec_espelho

/-- info: 'ClayRiemannProof.Leis.vec_torcao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.vec_torcao

/-- info: 'ClayRiemannProof.Leis.klein' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.klein

/-- info: 'ClayRiemannProof.Leis.produto_quarteto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.produto_quarteto

/-- info: 'ClayRiemannProof.Leis.produto_na_reta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.produto_na_reta

/-- info: 'ClayRiemannProof.Leis.target_iff_fora_vazio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.target_iff_fora_vazio

/-- info: 'ClayRiemannProof.Leis.orbita_sub_fora' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.orbita_sub_fora

/-- info: 'ClayRiemannProof.Leis.fora_vazio_ou_quatro' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.fora_vazio_ou_quatro

/-- info: 'ClayRiemannProof.Leis.classes_orbita' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.classes_orbita

/-- info: 'ClayRiemannProof.Leis.sem_habitantes_ate_13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.sem_habitantes_ate_13

/-- info: 'ClayRiemannProof.Leis.fora_ate_janela_vazio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.fora_ate_janela_vazio

/-- info: 'ClayRiemannProof.Leis.fora_em_pares' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.fora_em_pares

/-- info: 'ClayRiemannProof.Leis.deficit_ao_menos_dois' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.deficit_ao_menos_dois

/-- info: 'ClayRiemannProof.Leis.fora_ate_continuacao_vazio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Leis.fora_ate_continuacao_vazio

/-- info: 'ClayRiemannProof.PrimeiroFora.JanelaArb2026' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.PrimeiroFora.JanelaArb2026

/-! ## `ClayRiemannProof/Correcoes.lean` -/

/-- info: 'ClayRiemannProof.Correcoes.par_fora_na_janela' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.par_fora_na_janela

/-- info: 'ClayRiemannProof.Correcoes.S_sobe_no_par' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.S_sobe_no_par

/-- info: 'ClayRiemannProof.Correcoes.par_fora_da_caixa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.par_fora_da_caixa

/-- info: 'ClayRiemannProof.Correcoes.bForcado' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.bForcado

/-- info: 'ClayRiemannProof.Correcoes.bForcado_eh_desvio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.bForcado_eh_desvio

/-- info: 'ClayRiemannProof.Correcoes.b_na_colisao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.b_na_colisao

/-- info: 'ClayRiemannProof.Correcoes.metade_raiz_entre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.metade_raiz_entre

/-- info: 'ClayRiemannProof.Correcoes.par6_forcado' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.par6_forcado

/-- info: 'ClayRiemannProof.Correcoes.par6_valores_errados' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.par6_valores_errados

/-- info: 'ClayRiemannProof.Correcoes.rh_iff_lambda_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.rh_iff_lambda_zero

/-- info: 'ClayRiemannProof.Correcoes.lambda_negativo_impossivel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.lambda_negativo_impossivel

/-- info: 'ClayRiemannProof.Correcoes.cota_de_lehmer_mais_fraca' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.cota_de_lehmer_mais_fraca

/-- info: 'ClayRiemannProof.Correcoes.gram_k_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.gram_k_zeros

/-- info: 'ClayRiemannProof.Correcoes.gram_quadruplo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.gram_quadruplo

/-- info: 'ClayRiemannProof.Correcoes.janelaNaReta_de_fora_vazio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.janelaNaReta_de_fora_vazio

/-- info: 'ClayRiemannProof.Correcoes.janelaNaReta_restringe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.janelaNaReta_restringe

/-- info: 'ClayRiemannProof.Correcoes.faixa_na_reta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.faixa_na_reta

/-- info: 'ClayRiemannProof.Correcoes.continuacao_de_contagens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.continuacao_de_contagens

/-- info: 'ClayRiemannProof.Correcoes.janelaContinuacao_de_contagens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.janelaContinuacao_de_contagens

/-- info: 'ClayRiemannProof.Correcoes.rhAteZ_de_contagens' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.rhAteZ_de_contagens

/-- info: 'ClayRiemannProof.Correcoes.h2_fatora' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.h2_fatora

/-- info: 'ClayRiemannProof.Correcoes.zeros_nunca_somem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.zeros_nunca_somem

/-- info: 'ClayRiemannProof.Correcoes.colisao_zero_duplo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.colisao_zero_duplo

/-- info: 'ClayRiemannProof.Correcoes.depois_da_colisao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Correcoes.depois_da_colisao
