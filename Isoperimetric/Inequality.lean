import Isoperimetric.Arclength
import Isoperimetric.Boundary

noncomputable section

open Set MeasureTheory MeasureTheory.Measure

namespace Isoperimetric

/-- The full area-length inequality for an arbitrary continuous rectifiable Jordan
parametrization, with no orientation or smoothness hypothesis. -/
theorem RectifiableJordan.isoperimetric {γ : ℝ → Plane} (h : RectifiableJordan γ) :
    4 * Real.pi * area γ ≤ length γ ^ 2 := by
  have hi := planar_boundary_inequality (enclosed γ) h.measurableSet_enclosed
    h.enclosed_properties.2.2
  rw [h.frontier_enclosed, h.hausdorffMeasure_trace] at hi
  have hfinite : eVariationOn γ (Icc 0 1) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top h.eVariationOn_ne_top
  have hr := ENNReal.toReal_mono hfinite hi
  simpa [area, length, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal Real.pi_pos.le, mul_comm, mul_left_comm, mul_assoc] using hr

end Isoperimetric
