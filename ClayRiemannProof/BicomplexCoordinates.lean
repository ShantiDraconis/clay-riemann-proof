import Mathlib

/-!
# Bicomplex coordinate algebra (supplementary)

This module formalizes finite algebraic coordinate identities only. It does not
define a bicomplex extension of the Riemann zeta function and proves no RH claim.
-/

namespace ClayRiemannProof.BicomplexCoordinates

/-- A point on a vertical line in the ordinary complex plane. -/
def verticalPoint (sigma t : ℝ) : ℂ := ⟨sigma, t⟩

/-- Changing the imaginary coordinate does not change the real coordinate. -/
theorem re_verticalPoint (sigma t : ℝ) :
    (verticalPoint sigma t).re = sigma := rfl

theorem re_verticalPoint_eq_of_same_sigma (sigma t₁ t₂ : ℝ) :
    (verticalPoint sigma t₁).re = (verticalPoint sigma t₂).re := rfl

/-- The real-coordinate version of the user's 2 Re(s)=1 calculation. -/
theorem critical_coordinate_eq_half (sigma : ℝ) (h : 2 * sigma = 1) :
    sigma = (1 / 2 : ℝ) := by
  linarith

theorem neg_half_of_critical_coordinate (sigma : ℝ) (h : 2 * sigma = 1) :
    (-sigma / 2 : ℝ) = -(1 / 4 : ℝ) ∧
      (-sigma / 2 : ℝ) ≠ (1 / 2 : ℝ) := by
  constructor <;> nlinarith

/-- Coordinates r + i*iPart + j*jPart + (ij)*kPart, with commuting i,j
and i² = j² = -1. -/
structure BC where
  re : Int
  iPart : Int
  jPart : Int
  kPart : Int
  deriving DecidableEq, Repr

def zero : BC := ⟨0, 0, 0, 0⟩
def one : BC := ⟨1, 0, 0, 0⟩
def basisI : BC := ⟨0, 1, 0, 0⟩
def basisJ : BC := ⟨0, 0, 1, 0⟩
def basisK : BC := ⟨0, 0, 0, 1⟩

def add (x y : BC) : BC :=
  ⟨x.re + y.re, x.iPart + y.iPart, x.jPart + y.jPart, x.kPart + y.kPart⟩

def neg (x : BC) : BC := ⟨-x.re, -x.iPart, -x.jPart, -x.kPart⟩
def sub (x y : BC) : BC := add x (neg y)

/-- Bicomplex multiplication in the basis 1,i,j,k, where k=ij. -/
def mul (x y : BC) : BC :=
  ⟨ x.re * y.re - x.iPart * y.iPart - x.jPart * y.jPart + x.kPart * y.kPart,
    x.re * y.iPart + x.iPart * y.re - x.jPart * y.kPart - x.kPart * y.jPart,
    x.re * y.jPart + x.jPart * y.re - x.iPart * y.kPart - x.kPart * y.iPart,
    x.re * y.kPart + x.kPart * y.re + x.iPart * y.jPart + x.jPart * y.iPart ⟩

theorem i_sq : mul basisI basisI = neg one := by decide
theorem j_sq : mul basisJ basisJ = neg one := by decide
theorem ij_eq_k : mul basisI basisJ = basisK := by decide
theorem ji_eq_k : mul basisJ basisI = basisK := by decide
theorem k_sq : mul basisK basisK = one := by decide

theorem j_inverse_left : mul basisJ (neg basisJ) = one := by decide
theorem j_inverse_right : mul (neg basisJ) basisJ = one := by decide

/-- Euclidean coordinate norm squared; this is not asserted to be
multiplicative for bicomplex multiplication. -/
def coordinateNormSq (x : BC) : Int :=
  x.re ^ 2 + x.iPart ^ 2 + x.jPart ^ 2 + x.kPart ^ 2

theorem j_coordinate_norm_sq : coordinateNormSq basisJ = 1 := by decide

/-- (1+k) and (1-k) are nonzero zero divisors. -/
theorem idempotent_zero_divisors :
    mul (add one basisK) (sub one basisK) = zero := by decide

theorem one_add_k_ne_zero : add one basisK ≠ zero := by decide
theorem one_sub_k_ne_zero : sub one basisK ≠ zero := by decide

/-- Embed a + i b in the first complex plane. -/
def complexEmbed (a b : Int) : BC := ⟨a, b, 0, 0⟩

/-- Embed a + j b using an independent commuting unit j. -/
def secondPlaneEmbed (a b : Int) : BC := ⟨a, 0, b, 0⟩

def iTimes (x : BC) : BC := mul basisI x

/-- With the same complex unit, i(a+ib) = -b+ia. -/
theorem i_mul_complex (a b : Int) :
    iTimes (complexEmbed a b) = ⟨-b, a, 0, 0⟩ := by
  simp [iTimes, mul, basisI, complexEmbed]

/-- With independent j, i(a+jb)=ia+kb; the scalar real coordinate
does not shift. -/
theorem i_mul_second_plane (a b : Int) :
    iTimes (secondPlaneEmbed a b) = ⟨0, a, 0, b⟩ := by
  simp [iTimes, mul, basisI, secondPlaneEmbed]

theorem real_minus_one_plus_i_complex_y (a b : Int) :
    (add (complexEmbed (-1) 0) (iTimes (complexEmbed a b))).re = -1 - b := by
  rw [i_mul_complex]
  change -1 + (-b) = -1 - b
  ring

theorem real_minus_one_plus_i_real_y (a : Int) :
    (add (complexEmbed (-1) 0) (iTimes (complexEmbed a 0))).re = -1 := by
  rw [i_mul_complex]
  rfl

theorem real_minus_one_plus_i_independent_j (a b : Int) :
    (add (complexEmbed (-1) 0) (iTimes (secondPlaneEmbed a b))).re = -1 := by
  rw [i_mul_second_plane]
  rfl

/-- In ordinary complex arithmetic, Re(-1 + i(0-3i)) = 2. -/
theorem complex_y_example_re_two :
    (add (complexEmbed (-1) 0) (iTimes (complexEmbed 0 (-3)))).re = 2 := by
  decide

/-- The two idempotent components of sigma + it + kb have real
coordinates sigma+b and sigma-b. -/
def componentPlus (sigma t b : Int) : Int × Int := (sigma + b, t)
def componentMinus (sigma t b : Int) : Int × Int := (sigma - b, t)

theorem projection_b_zero (sigma t : Int) :
    componentPlus sigma t 0 = (sigma, t) ∧
    componentMinus sigma t 0 = (sigma, t) := by
  simp [componentPlus, componentMinus]

end ClayRiemannProof.BicomplexCoordinates
