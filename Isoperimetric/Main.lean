/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Isoperimetric.Topology.Orientation
import Isoperimetric.Inequality
import Isoperimetric.Circle

/-!
# Classical planar isoperimetry, including rigidity

Assemble the geometric inequality, orientation-free circle rigidity and the circle converse.
`classical_isoperimetric` exposes the four elementary hypotheses explicitly;
`classical_isoperimetric_specification` proves the proposition recorded in the specification.
-/

noncomputable section

open Set MeasureTheory

namespace Isoperimetric

variable {γ : ℝ → Plane}

/-- Equality in the geometric isoperimetric inequality forces a positive-radius circle.
The original parametrization need only be continuous, closed, simple and rectifiable. -/
theorem RectifiableJordan.circle_of_area_equality (h : RectifiableJordan γ)
    (heq : 4 * Real.pi * area γ = length γ ^ 2) :
    ∃ (c : Plane) (r : ℝ), 0 < r ∧ trace γ = Metric.sphere c r := by
  obtain ⟨b, hb⟩ := h.exists_orientation
  exact h.circle_of_area_equality_of_orientation b hb heq

/-- The full classical planar isoperimetric theorem,
including equality exactly for circle images. -/
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
theorem classical_isoperimetric_specification : ClassicalIsoperimetric :=
  fun _ h ↦ h.classical_isoperimetric

end Isoperimetric
