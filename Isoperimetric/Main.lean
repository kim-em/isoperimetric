import Isoperimetric.Topology.Orientation
import Isoperimetric.Inequality

noncomputable section

open Set MeasureTheory

namespace Isoperimetric

variable {γ : ℝ → Plane}

/-- Equality in the geometric isoperimetric inequality forces a positive-radius circle.
The original parametrization need only be continuous, closed, simple and rectifiable. -/
theorem RectifiableJordan.circle_of_area_equality (h : RectifiableJordan γ)
    (heq : 4 * Real.pi * area γ = length γ ^ 2) :
    ∃ (c : Plane) (r : ℝ), 0 < r ∧ trace γ = Metric.sphere c r := by
  obtain ⟨b, hb⟩ := h.exists_orientation_arclength
  have ha := h.arclengthParam_isRectifiableJordan
  have heq' : 4 * Real.pi * area (arclengthParam γ) = length (arclengthParam γ) ^ 2 := by
    rw [h.area_arclengthParam, h.length_arclengthParam]
    exact heq
  obtain ⟨c, r, hr, htrace⟩ := ha.circle_of_area_equality_of_orientation b hb heq'
  rw [h.trace_arclengthParam] at htrace
  exact ⟨c, r, hr, htrace⟩

/-- The full classical planar isoperimetric theorem, including equality exactly for circle images. -/
theorem RectifiableJordan.classical_isoperimetric (h : RectifiableJordan γ) :
    4 * Real.pi * area γ ≤ length γ ^ 2 ∧
      (4 * Real.pi * area γ = length γ ^ 2 ↔
        ∃ (c : Plane) (r : ℝ), 0 < r ∧ trace γ = Metric.sphere c r) := by
  refine ⟨h.isoperimetric, h.circle_of_area_equality, ?_⟩
  rintro ⟨c, r, hr, htrace⟩
  exact h.equality_of_circle c r hr htrace

/-- A public formulation with precisely the four geometric hypotheses, and with
length and area defined by total variation and genuine Jordan-interior volume. -/
theorem classical_isoperimetric (γ : ℝ → EuclideanSpace ℝ (Fin 2))
    (hcontinuous : ContinuousOn γ (Icc 0 1)) (hclosed : γ 0 = γ 1)
    (hsimple : InjOn γ (Ico 0 1)) (hrectifiable : BoundedVariationOn γ (Icc 0 1)) :
    4 * Real.pi * area γ ≤ length γ ^ 2 ∧
      (4 * Real.pi * area γ = length γ ^ 2 ↔
        ∃ (c : Plane) (r : ℝ), 0 < r ∧ trace γ = Metric.sphere c r) :=
  (⟨hcontinuous, hclosed, hsimple, hrectifiable⟩ : RectifiableJordan γ).classical_isoperimetric

/-- The complete target proposition from the original specification. -/
theorem classicalIsoperimetric : ClassicalIsoperimetric :=
  fun _ h ↦ h.classical_isoperimetric

end Isoperimetric
