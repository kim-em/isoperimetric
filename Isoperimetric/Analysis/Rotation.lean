import Isoperimetric.Statement

noncomputable section

namespace Isoperimetric

/-- The usual oriented planar determinant. -/
def determinant (z v : Plane) : ℝ := z 0 * v 1 - z 1 * v 0

private def quarterTurnLinear : Plane →ₗ[ℝ] Plane where
  toFun z := WithLp.toLp 2 ![-z 1, z 0]
  map_add' z v := by
    ext i
    fin_cases i <;> simp [add_comm]
  map_smul' r z := by
    ext i
    fin_cases i <;> simp

/-- Counterclockwise rotation through ninety degrees. -/
def quarterTurn : Plane →L[ℝ] Plane := quarterTurnLinear.toContinuousLinearMap

@[simp] theorem quarterTurn_zero (z : Plane) : quarterTurn z 0 = -z 1 := rfl
@[simp] theorem quarterTurn_one (z : Plane) : quarterTurn z 1 = z 0 := rfl

theorem norm_quarterTurn (z : Plane) : ‖quarterTurn z‖ = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [MovingSofa.Point.norm_sq_eq, quarterTurn_zero, quarterTurn_one, neg_sq]
  ring

/-- The pointwise algebra behind the rigidity argument. -/
theorem norm_sub_quarterTurn_sq (z v : Plane) (ω : ℝ) :
    ‖v - ω • quarterTurn z‖ ^ 2 =
      ‖v‖ ^ 2 + ω ^ 2 * ‖z‖ ^ 2 - 2 * ω * determinant z v := by
  simp only [MovingSofa.Point.norm_sq_eq, PiLp.sub_apply, PiLp.smul_apply,
    quarterTurn_zero, quarterTurn_one, smul_eq_mul, determinant]
  ring

theorem determinant_sub_left (z c v : Plane) :
    determinant (z - c) v = determinant z v - determinant c v := by
  simp only [determinant, PiLp.sub_apply]
  ring

/-- The standard real linear isometry from the plane to the complex numbers. -/
def planeComplex : Plane ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm

@[simp] theorem planeComplex_apply (z : Plane) :
    planeComplex z = (z 0 : ℂ) + (z 1 : ℂ) * Complex.I :=
  Complex.orthonormalBasisOneI_repr_symm_apply z

theorem planeComplex_quarterTurn (z : Plane) :
    planeComplex (quarterTurn z) = Complex.I * planeComplex z := by
  apply Complex.ext <;> simp [planeComplex_apply]


end Isoperimetric
