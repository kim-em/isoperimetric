/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Isoperimetric.BoundaryLength
import Isoperimetric.BoundaryInequality

/-!
# Area-length inequality for rectifiable Jordan curves

Apply the two-dimensional geometric boundary inequality to the bounded Jordan interior.
Its frontier is the trace, whose Hausdorff measure equals the finite variation length.
-/

noncomputable section

open Set MeasureTheory MeasureTheory.Measure

namespace Isoperimetric

/-- The full area-length inequality for an arbitrary continuous rectifiable Jordan
parametrization, with no orientation or smoothness hypothesis. -/
theorem RectifiableJordan.isoperimetric {γ : ℝ → Plane} (h : RectifiableJordan γ) :
    4 * Real.pi * area γ ≤ length γ ^ 2 := by
  have hi := planar_boundary_inequality (enclosed γ) h.measurableSet_enclosed
    h.isBounded_enclosed
  rw [h.frontier_enclosed, h.hausdorffMeasure_trace] at hi
  have hfinite : eVariationOn γ (Icc 0 1) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top h.eVariationOn_ne_top
  have hr := ENNReal.toReal_mono hfinite hi
  simpa [area, length, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal Real.pi_pos.le, mul_comm, mul_left_comm, mul_assoc] using hr

end Isoperimetric
