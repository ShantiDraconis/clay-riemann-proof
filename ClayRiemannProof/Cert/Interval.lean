import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Rat.Floor

/-!
# Aritmética de intervalos verificada sobre `ℚ`

Intervalos reais `[lo, hi]` com extremos racionais (`IR`) e retângulos complexos (`IC`). Cada operação vem
com um teorema de correção: se os argumentos estão nos intervalos, o resultado está no intervalo
calculado. As contas são em `ℚ` e podem ser verificadas pelo **kernel** (`decide +kernel`), sem
`native_decide`. O arredondamento para fora (`IR.round`) mantém os racionais pequenos.

Origem: ATK kernel (espelho público, M-Core `390e378`), `ATK/Cert/Intervalo.lean`; portado para Mathlib
`8fe7ce4`, nomes `ATK.Cert.*` → `ClayRiemannProof.Cert.Interval.*`, `import Mathlib` trocado por módulos
específicos, linhas `#print axioms` retiradas (os axiomas estão fixados em `ClayRiemannProof/AuditThirteen.lean`).
Só o fecho mínimo usado pela certificação da faixa até a altura 13 foi portado (retirados `IR.inv`,
`IR.absMax`, `IR.mem_widen`, `IC.sub`, `IC.normMax`, `IC.mem_widen` e os teoremas correspondentes).
-/

namespace ClayRiemannProof.Cert.Interval

/-- Intervalo real com extremos racionais. -/
structure IR where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

/-- Retângulo complexo. -/
structure IC where
  re : IR
  im : IR
  deriving DecidableEq, Repr

namespace IR

def mem (x : ℝ) (I : IR) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ I.hi

def pt (q : ℚ) : IR := ⟨q, q⟩

def add (I J : IR) : IR := ⟨I.lo + J.lo, I.hi + J.hi⟩

def neg (I : IR) : IR := ⟨-I.hi, -I.lo⟩

def sub (I J : IR) : IR := add I (neg J)

def mul (I J : IR) : IR :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩

/-- Alarga por `e ≥ 0` dos dois lados. -/
def widen (I : IR) (e : ℚ) : IR := ⟨I.lo - e, I.hi + e⟩

/-- Arredondamento para fora na precisão `2^{-p}`. -/
def round (p : ℕ) (I : IR) : IR :=
  ⟨(⌊I.lo * 2 ^ p⌋ : ℚ) / 2 ^ p, (⌈I.hi * 2 ^ p⌉ : ℚ) / 2 ^ p⟩

theorem mem_pt (q : ℚ) : mem (q : ℝ) (pt q) := ⟨le_rfl, le_rfl⟩

theorem mem_add {x y : ℝ} {I J : IR} (hx : mem x I) (hy : mem y J) : mem (x + y) (add I J) := by
  unfold mem add at *; push_cast; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem mem_neg {x : ℝ} {I : IR} (hx : mem x I) : mem (-x) (neg I) := by
  unfold mem neg at *; push_cast; constructor <;> linarith [hx.1, hx.2]

theorem mem_sub {x y : ℝ} {I J : IR} (hx : mem x I) (hy : mem y J) : mem (x - y) (sub I J) := by
  rw [sub_eq_add_neg]; exact mem_add hx (mem_neg hy)

theorem min_le_mul {a b x y : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) : min (a * y) (b * y) ≤ x * y := by
  rcases le_total 0 y with hy | hy
  · exact (min_le_left _ _).trans (by nlinarith)
  · exact (min_le_right _ _).trans (by nlinarith)

theorem mul_le_max {a b x y : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) : x * y ≤ max (a * y) (b * y) := by
  rcases le_total 0 y with hy | hy
  · exact (by nlinarith : x * y ≤ b * y).trans (le_max_right _ _)
  · exact (by nlinarith : x * y ≤ a * y).trans (le_max_left _ _)

theorem mem_mul {x y : ℝ} {I J : IR} (hx : mem x I) (hy : mem y J) : mem (x * y) (mul I J) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  unfold mem mul
  push_cast
  constructor
  · have h1 := min_le_mul (y := y) hx1 hx2
    have h2 : min ((I.lo : ℝ) * J.lo) ((I.lo : ℝ) * J.hi) ≤ (I.lo : ℝ) * y := by
      have := min_le_mul (y := (I.lo : ℝ)) hy1 hy2
      simpa [mul_comm] using this
    have h3 : min ((I.hi : ℝ) * J.lo) ((I.hi : ℝ) * J.hi) ≤ (I.hi : ℝ) * y := by
      have := min_le_mul (y := (I.hi : ℝ)) hy1 hy2
      simpa [mul_comm] using this
    calc min (min ((I.lo : ℝ) * J.lo) ((I.lo : ℝ) * J.hi)) (min ((I.hi : ℝ) * J.lo) ((I.hi : ℝ) * J.hi))
        ≤ min ((I.lo : ℝ) * y) ((I.hi : ℝ) * y) := min_le_min h2 h3
      _ ≤ x * y := h1
  · have h1 := mul_le_max (y := y) hx1 hx2
    have h2 : (I.lo : ℝ) * y ≤ max ((I.lo : ℝ) * J.lo) ((I.lo : ℝ) * J.hi) := by
      have := mul_le_max (y := (I.lo : ℝ)) hy1 hy2
      simpa [mul_comm] using this
    have h3 : (I.hi : ℝ) * y ≤ max ((I.hi : ℝ) * J.lo) ((I.hi : ℝ) * J.hi) := by
      have := mul_le_max (y := (I.hi : ℝ)) hy1 hy2
      simpa [mul_comm] using this
    calc x * y ≤ max ((I.lo : ℝ) * y) ((I.hi : ℝ) * y) := h1
      _ ≤ _ := max_le_max h2 h3

/-- Um ponto a distância `≤ e` de um ponto de `I` está em `I` alargado por `e`. -/
theorem mem_widen_of_dist {x y : ℝ} {I : IR} {e : ℚ} (hy : mem y I) (h : |x - y| ≤ e) :
    mem x (widen I e) := by
  unfold mem widen at *; push_cast
  have := abs_le.mp h
  constructor <;> linarith [hy.1, hy.2, this.1, this.2]

theorem mem_round {x : ℝ} {I : IR} (p : ℕ) (hx : mem x I) : mem x (round p I) := by
  obtain ⟨h1, h2⟩ := hx
  have hp : (0 : ℚ) < 2 ^ p := by positivity
  unfold mem round
  constructor
  · have : ((⌊I.lo * 2 ^ p⌋ : ℚ) / 2 ^ p) ≤ I.lo := by
      rw [div_le_iff₀ hp]; exact Int.floor_le _
    exact le_trans (by exact_mod_cast this) h1
  · have : I.hi ≤ ((⌈I.hi * 2 ^ p⌉ : ℚ) / 2 ^ p) := by
      rw [le_div_iff₀ hp]; exact Int.le_ceil _
    exact le_trans h2 (by exact_mod_cast this)

end IR

namespace IC

def mem (z : ℂ) (I : IC) : Prop := IR.mem z.re I.re ∧ IR.mem z.im I.im

def pt (a b : ℚ) : IC := ⟨IR.pt a, IR.pt b⟩

def add (I J : IC) : IC := ⟨IR.add I.re J.re, IR.add I.im J.im⟩

def mul (I J : IC) : IC :=
  ⟨IR.sub (IR.mul I.re J.re) (IR.mul I.im J.im), IR.add (IR.mul I.re J.im) (IR.mul I.im J.re)⟩

/-- Multiplicação por um real num intervalo. -/
def smul (K : IR) (I : IC) : IC := ⟨IR.mul K I.re, IR.mul K I.im⟩

def widen (I : IC) (e : ℚ) : IC := ⟨IR.widen I.re e, IR.widen I.im e⟩

def round (p : ℕ) (I : IC) : IC := ⟨IR.round p I.re, IR.round p I.im⟩

theorem mem_pt (a b : ℚ) : mem ((a : ℂ) + (b : ℂ) * Complex.I) (pt a b) := by
  unfold mem pt IR.mem IR.pt; simp

theorem mem_add {z w : ℂ} {I J : IC} (hz : mem z I) (hw : mem w J) : mem (z + w) (add I J) :=
  ⟨by simpa [add] using IR.mem_add hz.1 hw.1, by simpa [add] using IR.mem_add hz.2 hw.2⟩

theorem mem_mul {z w : ℂ} {I J : IC} (hz : mem z I) (hw : mem w J) : mem (z * w) (mul I J) := by
  constructor
  · rw [Complex.mul_re]; exact IR.mem_sub (IR.mem_mul hz.1 hw.1) (IR.mem_mul hz.2 hw.2)
  · rw [Complex.mul_im]; exact IR.mem_add (IR.mem_mul hz.1 hw.2) (IR.mem_mul hz.2 hw.1)

theorem mem_smul {x : ℝ} {z : ℂ} {K : IR} {I : IC} (hx : IR.mem x K) (hz : mem z I) :
    mem ((x : ℂ) * z) (smul K I) := by
  constructor
  · simpa [smul] using IR.mem_mul hx hz.1
  · simpa [smul] using IR.mem_mul hx hz.2

theorem mem_round {z : ℂ} {I : IC} (p : ℕ) (hz : mem z I) : mem z (round p I) :=
  ⟨IR.mem_round p hz.1, IR.mem_round p hz.2⟩

/-- Um ponto a distância `≤ e` (em norma) de um ponto de `I` está em `I` alargado por `e`. -/
theorem mem_widen_of_norm {z w : ℂ} {I : IC} {e : ℚ} (hw : mem w I) (h : ‖z - w‖ ≤ e) :
    mem z (widen I e) := by
  constructor
  · refine IR.mem_widen_of_dist hw.1 ?_
    have := Complex.abs_re_le_norm (z - w)
    rw [Complex.sub_re] at this; linarith
  · refine IR.mem_widen_of_dist hw.2 ?_
    have := Complex.abs_im_le_norm (z - w)
    rw [Complex.sub_im] at this; linarith

end IC

end ClayRiemannProof.Cert.Interval
