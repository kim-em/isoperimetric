import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
The geometric objects and the intended public proposition. No analytic identities,
orientation choice, or area formula are included in the curve hypotheses.
-/

noncomputable section

open Set MeasureTheory

namespace Isoperimetric

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A continuous rectifiable once-traversal, with the two endpoints identified. -/
structure RectifiableJordan (γ : ℝ → Plane) : Prop where
  continuousOn : ContinuousOn γ (Icc 0 1)
  closed : γ 0 = γ 1
  injectiveOn : InjOn γ (Ico 0 1)
  boundedVariationOn : BoundedVariationOn γ (Icc 0 1)

/-- The geometric trace, including the identified endpoints. -/
def trace (γ : ℝ → Plane) : Set Plane := γ '' Icc 0 1

/-- The bounded connected components of the complement of the trace. -/
def enclosed (γ : ℝ → Plane) : Set Plane :=
  {p | p ∉ trace γ ∧ Bornology.IsBounded (connectedComponentIn (trace γ)ᶜ p)}

/-- Geometric length; its finiteness must be proved before using `toReal`. -/
def length (γ : ℝ → Plane) : ℝ := (eVariationOn γ (Icc 0 1)).toReal

/-- Actual Lebesgue area; its finiteness must be proved before using `toReal`. -/
def area (γ : ℝ → Plane) : ℝ := (volume (enclosed γ)).toReal

/-- The geometric target proposition, proved by `classicalIsoperimetric` in `Main.lean`. -/
def ClassicalIsoperimetric : Prop :=
  ∀ (γ : ℝ → Plane), RectifiableJordan γ →
    4 * Real.pi * area γ ≤ length γ ^ 2 ∧
    (4 * Real.pi * area γ = length γ ^ 2 ↔
      ∃ (c : Plane) (r : ℝ), 0 < r ∧ trace γ = Metric.sphere c r)

end Isoperimetric
