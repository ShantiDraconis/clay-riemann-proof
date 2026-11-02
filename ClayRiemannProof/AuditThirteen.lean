import ClayRiemannProof.Cert.Interval
import ClayRiemannProof.Cert.Transcendental
import ClayRiemannProof.EulerMaclaurin.FirstOrder
import ClayRiemannProof.EulerMaclaurin.General
import ClayRiemannProof.CertifiedZeros.EulerMaclaurinData
import ClayRiemannProof.CertifiedZeros.CrudeBound
import ClayRiemannProof.CertifiedZeros.Evaluation
import ClayRiemannProof.CertifiedZeros.Rectangle
import ClayRiemannProof.CertifiedZeros.Pieces1
import ClayRiemannProof.CertifiedZeros.Pieces2
import ClayRiemannProof.CertifiedZeros.Pieces3
import ClayRiemannProof.LowStrip.Disc
import ClayRiemannProof.HeightThirteen

/-!
# Auditoria de axiomas: a faixa sem zeros até a altura 13 e o mundo `Z = 13`

Um `#guard_msgs in #print axioms X` para cada uma das 252 declarações públicas acrescentadas por
`ClayRiemannProof/HeightThirteen.lean` e pelos módulos que ele importa (saída real do Lean). Se aparecer
qualquer axioma diferente de `propext`, `Classical.choice`, `Quot.sound` (inclusive `sorryAx`), a compilação falha.

Os certificados numéricos (`CertifiedZeros/Pieces1`–`3`) usam `decide +kernel`, que não acrescenta axioma: a
verificação é feita pelo próprio kernel, sem `native_decide` (que acrescentaria `Lean.ofReduceBool`).

`Classical.choice` vem do Mathlib: `#print axioms Real` já dá `[propext, Classical.choice, Quot.sound]`.
-/


/-! ## `ClayRiemannProof/Cert/Interval.lean` -/

/-- info: 'ClayRiemannProof.Cert.Interval.IR' does not depend on any axioms -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IR

/-- info: 'ClayRiemannProof.Cert.Interval.IC' does not depend on any axioms -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IC

/-- info: 'ClayRiemannProof.Cert.Interval.IR.mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IR.mem

/-- info: 'ClayRiemannProof.Cert.Interval.IR.pt' does not depend on any axioms -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IR.pt

/-- info: 'ClayRiemannProof.Cert.Interval.IR.add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IR.add

/-- info: 'ClayRiemannProof.Cert.Interval.IR.neg' does not depend on any axioms -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IR.neg

/-- info: 'ClayRiemannProof.Cert.Interval.IR.sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IR.sub

/-- info: 'ClayRiemannProof.Cert.Interval.IR.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IR.mul

/-- info: 'ClayRiemannProof.Cert.Interval.IR.widen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IR.widen

/-- info: 'ClayRiemannProof.Cert.Interval.IR.round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IR.round

/-- info: 'ClayRiemannProof.Cert.Interval.IR.mem_pt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IR.mem_pt

/-- info: 'ClayRiemannProof.Cert.Interval.IR.mem_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IR.mem_add

/-- info: 'ClayRiemannProof.Cert.Interval.IR.mem_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IR.mem_neg

/-- info: 'ClayRiemannProof.Cert.Interval.IR.mem_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IR.mem_sub

/-- info: 'ClayRiemannProof.Cert.Interval.IR.min_le_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IR.min_le_mul

/-- info: 'ClayRiemannProof.Cert.Interval.IR.mul_le_max' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IR.mul_le_max

/-- info: 'ClayRiemannProof.Cert.Interval.IR.mem_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IR.mem_mul

/-- info: 'ClayRiemannProof.Cert.Interval.IR.mem_widen_of_dist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IR.mem_widen_of_dist

/-- info: 'ClayRiemannProof.Cert.Interval.IR.mem_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IR.mem_round

/-- info: 'ClayRiemannProof.Cert.Interval.IC.mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IC.mem

/-- info: 'ClayRiemannProof.Cert.Interval.IC.pt' does not depend on any axioms -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IC.pt

/-- info: 'ClayRiemannProof.Cert.Interval.IC.add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IC.add

/-- info: 'ClayRiemannProof.Cert.Interval.IC.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IC.mul

/-- info: 'ClayRiemannProof.Cert.Interval.IC.smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IC.smul

/-- info: 'ClayRiemannProof.Cert.Interval.IC.widen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IC.widen

/-- info: 'ClayRiemannProof.Cert.Interval.IC.round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IC.round

/-- info: 'ClayRiemannProof.Cert.Interval.IC.mem_pt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IC.mem_pt

/-- info: 'ClayRiemannProof.Cert.Interval.IC.mem_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IC.mem_add

/-- info: 'ClayRiemannProof.Cert.Interval.IC.mem_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IC.mem_mul

/-- info: 'ClayRiemannProof.Cert.Interval.IC.mem_smul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IC.mem_smul

/-- info: 'ClayRiemannProof.Cert.Interval.IC.mem_round' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IC.mem_round

/-- info: 'ClayRiemannProof.Cert.Interval.IC.mem_widen_of_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Interval.IC.mem_widen_of_norm


/-! ## `ClayRiemannProof/Cert/Transcendental.lean` -/

/-- info: 'ClayRiemannProof.Cert.Transcendental.tayI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Transcendental.tayI

/-- info: 'ClayRiemannProof.Cert.Transcendental.tayI_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Transcendental.tayI_spec

/-- info: 'ClayRiemannProof.Cert.Transcendental.expIRect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Transcendental.expIRect

/-- info: 'ClayRiemannProof.Cert.Transcendental.mem_expIRect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Transcendental.mem_expIRect

/-- info: 'ClayRiemannProof.Cert.Transcendental.norm_expI_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Transcendental.norm_expI_sub_le

/-- info: 'ClayRiemannProof.Cert.Transcendental.piLo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Transcendental.piLo

/-- info: 'ClayRiemannProof.Cert.Transcendental.piLo_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Transcendental.piLo_lt

/-- info: 'ClayRiemannProof.Cert.Transcendental.lt_piLo_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Transcendental.lt_piLo_add

/-- info: 'ClayRiemannProof.Cert.Transcendental.redK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Transcendental.redK

/-- info: 'ClayRiemannProof.Cert.Transcendental.redM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Transcendental.redM

/-- info: 'ClayRiemannProof.Cert.Transcendental.redE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Transcendental.redE

/-- info: 'ClayRiemannProof.Cert.Transcendental.expIAuto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Transcendental.expIAuto

/-- info: 'ClayRiemannProof.Cert.Transcendental.expIAuto_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Transcendental.expIAuto_ok

/-- info: 'ClayRiemannProof.Cert.Transcendental.mem_expIAuto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Transcendental.mem_expIAuto

/-- info: 'ClayRiemannProof.Cert.Transcendental.atS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Transcendental.atS

/-- info: 'ClayRiemannProof.Cert.Transcendental.dLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Transcendental.dLog

/-- info: 'ClayRiemannProof.Cert.Transcendental.atS_cast' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Transcendental.atS_cast

/-- info: 'ClayRiemannProof.Cert.Transcendental.mem_dLog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.Cert.Transcendental.mem_dLog


/-! ## `ClayRiemannProof/EulerMaclaurin/FirstOrder.lean` -/

/-- info: 'ClayRiemannProof.EulerMaclaurin.FirstOrder.cauda' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.FirstOrder.cauda

/-- info: 'ClayRiemannProof.EulerMaclaurin.FirstOrder.integrableOn_cauda' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.FirstOrder.integrableOn_cauda

/-- info: 'ClayRiemannProof.EulerMaclaurin.FirstOrder.degrau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.FirstOrder.degrau

/-- info: 'ClayRiemannProof.EulerMaclaurin.FirstOrder.cauda_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.FirstOrder.cauda_split

/-- info: 'ClayRiemannProof.EulerMaclaurin.FirstOrder.zeta_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.FirstOrder.zeta_eq


/-! ## `ClayRiemannProof/EulerMaclaurin/General.lean` -/

/-- info: 'ClayRiemannProof.EulerMaclaurin.General.perB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.General.perB

/-- info: 'ClayRiemannProof.EulerMaclaurin.General.Cb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.General.Cb

/-- info: 'ClayRiemannProof.EulerMaclaurin.General.bernoulliFun_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.General.bernoulliFun_eq_sum

/-- info: 'ClayRiemannProof.EulerMaclaurin.General.abs_bernoulliFun_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.General.abs_bernoulliFun_le

/-- info: 'ClayRiemannProof.EulerMaclaurin.General.Cb_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.General.Cb_nonneg

/-- info: 'ClayRiemannProof.EulerMaclaurin.General.abs_perB_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.General.abs_perB_le

/-- info: 'ClayRiemannProof.EulerMaclaurin.General.measurable_perB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.General.measurable_perB

/-- info: 'ClayRiemannProof.EulerMaclaurin.General.perB_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.General.perB_eq

/-- info: 'ClayRiemannProof.EulerMaclaurin.General.J' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.General.J

/-- info: 'ClayRiemannProof.EulerMaclaurin.General.integrableOn_J' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.General.integrableOn_J

/-- info: 'ClayRiemannProof.EulerMaclaurin.General.norm_J_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.General.norm_J_le

/-- info: 'ClayRiemannProof.EulerMaclaurin.General.continuousOn_cpow_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.General.continuousOn_cpow_pos

/-- info: 'ClayRiemannProof.EulerMaclaurin.General.passo_unidade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.General.passo_unidade

/-- info: 'ClayRiemannProof.EulerMaclaurin.General.recorrencia' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.General.recorrencia

/-- info: 'ClayRiemannProof.EulerMaclaurin.General.poch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.General.poch

/-- info: 'ClayRiemannProof.EulerMaclaurin.General.EM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.General.EM

/-- info: 'ClayRiemannProof.EulerMaclaurin.General.cauda_eq_J' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.General.cauda_eq_J

/-- info: 'ClayRiemannProof.EulerMaclaurin.General.zeta_EM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.General.zeta_EM

/-- info: 'ClayRiemannProof.EulerMaclaurin.General.norm_zeta_sub_EM_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.EulerMaclaurin.General.norm_zeta_sub_EM_le


/-! ## `ClayRiemannProof/CertifiedZeros/EulerMaclaurinData.lean` -/

/-- info: 'ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.Lg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.Lg

/-- info: 'ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.fase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.fase

/-- info: 'ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.Btab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.Btab

/-- info: 'ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.pochQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.pochQ

/-- info: 'ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.PcR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.PcR

/-- info: 'ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.Qcoef' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.Qcoef

/-- info: 'ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.CbR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.CbR

/-- info: 'ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.mem_Lg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.mem_Lg

/-- info: 'ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.bp6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.bp6

/-- info: 'ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.bp8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.bp8

/-- info: 'ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.bp10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.bp10

/-- info: 'ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.bern_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.bern_eq

/-- info: 'ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.pochQ_spec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.pochQ_spec

/-- info: 'ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.PcR_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.PcR_spec

/-- info: 'ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.CbR_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.CbR_spec

/-- info: 'ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.EM_decomp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.EulerMaclaurinData.EM_decomp


/-! ## `ClayRiemannProof/CertifiedZeros/CrudeBound.lean` -/

/-- info: 'ClayRiemannProof.CertifiedZeros.CrudeBound.pochR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.CrudeBound.pochR

/-- info: 'ClayRiemannProof.CertifiedZeros.CrudeBound.pochR_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.CrudeBound.pochR_nonneg

/-- info: 'ClayRiemannProof.CertifiedZeros.CrudeBound.norm_poch_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.CrudeBound.norm_poch_le

/-- info: 'ClayRiemannProof.CertifiedZeros.CrudeBound.cota_geral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.CrudeBound.cota_geral

/-- info: 'ClayRiemannProof.CertifiedZeros.CrudeBound.pochRQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.CrudeBound.pochRQ

/-- info: 'ClayRiemannProof.CertifiedZeros.CrudeBound.somaBQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.CrudeBound.somaBQ

/-- info: 'ClayRiemannProof.CertifiedZeros.CrudeBound.cotaQ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.CrudeBound.cotaQ

/-- info: 'ClayRiemannProof.CertifiedZeros.CrudeBound.pochRQ_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.CrudeBound.pochRQ_spec

/-- info: 'ClayRiemannProof.CertifiedZeros.CrudeBound.somaBQ_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.CrudeBound.somaBQ_spec

/-- info: 'ClayRiemannProof.CertifiedZeros.CrudeBound.cotaQ_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.CrudeBound.cotaQ_spec


/-! ## `ClayRiemannProof/CertifiedZeros/Evaluation.lean` -/

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.rootOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.rootOk

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.mem_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.mem_root

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.cpow_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.cpow_gen

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.irootAux' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.irootAux

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.iroot' depends on axioms: [propext] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.iroot

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.powIG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.powIG

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.powOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.powOk

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.razao_sigma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.razao_sigma

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.mem_powIG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.mem_powIG

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.termoG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.termoG

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.somaG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.somaG

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.okTG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.okTG

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.okAllG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.okAllG

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.errQG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.errQG

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.zetaIG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.zetaIG

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.mem_termoG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.mem_termoG

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.mem_somaG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.mem_somaG

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.okAllG_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.okAllG_spec

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.N_divG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.N_divG

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.rpow_geral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.rpow_geral

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.resto_leG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.resto_leG

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.mem_zetaIG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.mem_zetaIG

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.dz' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.dz

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.nMinSq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.nMinSq

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.dz_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.dz_le

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.nMinSq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.nMinSq_le

/-- info: 'ClayRiemannProof.CertifiedZeros.Evaluation.le_norm_de' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Evaluation.le_norm_de


/-! ## `ClayRiemannProof/CertifiedZeros/Rectangle.lean` -/

/-- info: 'ClayRiemannProof.CertifiedZeros.Rectangle.certificado_malha' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Rectangle.certificado_malha

/-- info: 'ClayRiemannProof.CertifiedZeros.Rectangle.certificado_derivada' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Rectangle.certificado_derivada

/-- info: 'ClayRiemannProof.CertifiedZeros.Rectangle.difOn_zeta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Rectangle.difOn_zeta

/-- info: 'ClayRiemannProof.CertifiedZeros.Rectangle.cobre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Rectangle.cobre

/-- info: 'ClayRiemannProof.CertifiedZeros.Rectangle.ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Rectangle.ret

/-- info: 'ClayRiemannProof.CertifiedZeros.Rectangle.convex_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Rectangle.convex_ret

/-- info: 'ClayRiemannProof.CertifiedZeros.Rectangle.reg_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Rectangle.reg_ret

/-- info: 'ClayRiemannProof.CertifiedZeros.Rectangle.deriv_cota_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Rectangle.deriv_cota_ret

/-- info: 'ClayRiemannProof.CertifiedZeros.Rectangle.centrosR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Rectangle.centrosR

/-- info: 'ClayRiemannProof.CertifiedZeros.Rectangle.cobre_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Rectangle.cobre_ret

/-- info: 'ClayRiemannProof.CertifiedZeros.Rectangle.centrosR_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Rectangle.centrosR_ret

/-- info: 'ClayRiemannProof.CertifiedZeros.Rectangle.chkR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Rectangle.chkR

/-- info: 'ClayRiemannProof.CertifiedZeros.Rectangle.chkR_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Rectangle.chkR_spec

/-- info: 'ClayRiemannProof.CertifiedZeros.Rectangle.peca_ret' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Rectangle.peca_ret

/-- info: 'ClayRiemannProof.CertifiedZeros.Rectangle.ret_split_re' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Rectangle.ret_split_re

/-- info: 'ClayRiemannProof.CertifiedZeros.Rectangle.ret_split_im' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Rectangle.ret_split_im


/-! ## `ClayRiemannProof/CertifiedZeros/Pieces1.lean` -/

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.P4_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.P4_1

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.P4_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.P4_2

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.P4_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.P4_3

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.P4_4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.P4_4

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.P4_5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.P4_5

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.faixa_4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.faixa_4

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.P7_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.P7_1

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.faixa_7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.faixa_7

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.P9_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.P9_1

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.P9_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.P9_2

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.P9_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.P9_3

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.faixa_9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.faixa_9

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.P11_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.P11_1

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.P11_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.P11_2

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.P11_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.P11_3

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.P11_6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.P11_6

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.P11_7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.P11_7

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.P11_9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.P11_9

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.P11_10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.P11_10

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.P11_4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.P11_4

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.P11_5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.P11_5

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.P11_8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.P11_8

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.P11_11' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.P11_11

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.P11_12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.P11_12

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.P11_13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.P11_13

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces1.faixa_11' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces1.faixa_11


/-! ## `ClayRiemannProof/CertifiedZeros/Pieces2.lean` -/

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P0_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P0_1

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P0_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P0_2

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P0_4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P0_4

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P0_6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P0_6

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P0_7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P0_7

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P0_10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P0_10

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P0_11' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P0_11

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P0_13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P0_13

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P0_14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P0_14

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P0_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P0_3

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P0_5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P0_5

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P0_8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P0_8

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P0_9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P0_9

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P0_12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P0_12

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P0_15' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P0_15

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P0_16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P0_16

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P0_17' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P0_17

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.faixa_0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.faixa_0

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P3_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P3_1

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P3_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P3_2

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P3_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P3_3

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.faixa_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.faixa_3

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P6_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P6_1

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P6_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P6_2

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P6_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P6_3

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.faixa_6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.faixa_6

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P10_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P10_1

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P10_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P10_2

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P10_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P10_3

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P10_4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P10_4

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.P10_5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.P10_5

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces2.faixa_10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces2.faixa_10


/-! ## `ClayRiemannProof/CertifiedZeros/Pieces3.lean` -/

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P1_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P1_1

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P1_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P1_2

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P1_4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P1_4

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P1_5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P1_5

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P1_8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P1_8

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P1_9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P1_9

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P1_11' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P1_11

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P1_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P1_3

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P1_6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P1_6

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P1_7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P1_7

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P1_10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P1_10

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P1_12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P1_12

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P1_13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P1_13

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.faixa_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.faixa_1

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P2_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P2_1

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P2_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P2_2

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P2_4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P2_4

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P2_5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P2_5

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P2_8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P2_8

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P2_9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P2_9

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P2_11' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P2_11

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P2_12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P2_12

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P2_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P2_3

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P2_6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P2_6

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P2_7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P2_7

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P2_10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P2_10

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P2_13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P2_13

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P2_14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P2_14

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P2_15' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P2_15

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.faixa_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.faixa_2

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P5_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P5_1

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P5_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P5_2

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P5_4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P5_4

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P5_5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P5_5

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P5_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P5_3

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P5_6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P5_6

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P5_7' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P5_7

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.faixa_5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.faixa_5

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P8_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P8_1

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P8_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P8_2

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.P8_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.P8_3

/-- info: 'ClayRiemannProof.CertifiedZeros.Pieces3.faixa_8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.CertifiedZeros.Pieces3.faixa_8


/-! ## `ClayRiemannProof/LowStrip/Disc.lean` -/

/-- info: 'ClayRiemannProof.LowStrip.Disc.zeta_ne_zero_disco' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LowStrip.Disc.zeta_ne_zero_disco

/-- info: 'ClayRiemannProof.LowStrip.Disc.zeta_ne_zero_baixo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.LowStrip.Disc.zeta_ne_zero_baixo


/-! ## `ClayRiemannProof/HeightThirteen.lean` -/

/-- info: 'ClayRiemannProof.HeightThirteen.faixa_ate_13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.HeightThirteen.faixa_ate_13

/-- info: 'ClayRiemannProof.HeightThirteen.cota_metade' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.HeightThirteen.cota_metade

/-- info: 'ClayRiemannProof.HeightThirteen.im_torcao' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.HeightThirteen.im_torcao

/-- info: 'ClayRiemannProof.HeightThirteen.sem_zeros_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.HeightThirteen.sem_zeros_pos

/-- info: 'ClayRiemannProof.HeightThirteen.faixa_sem_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.HeightThirteen.faixa_sem_zeros

/-- info: 'ClayRiemannProof.HeightThirteen.zeros_acima_13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.HeightThirteen.zeros_acima_13

/-- info: 'ClayRiemannProof.HeightThirteen.rhNoMundo_13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms ClayRiemannProof.HeightThirteen.rhNoMundo_13
