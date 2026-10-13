/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Isoperimetric.Main

/-!
Check the public theorem against a statement written entirely with Mathlib objects.
The expected hypotheses and conclusion do not use the project's curve predicate,
trace, area, length, or interior definitions. Changing their mathematical meaning
must therefore satisfy this independent formulation as well.
-/

noncomputable section

open Set MeasureTheory

example (γ : ℝ → EuclideanSpace ℝ (Fin 2))
    (hcontinuous : ContinuousOn γ (Icc 0 1)) (hclosed : γ 0 = γ 1)
    (hsimple : InjOn γ (Ico 0 1)) (hrectifiable : BoundedVariationOn γ (Icc 0 1)) :
    let C := γ '' Icc (0 : ℝ) 1
    let A := (volume {p | p ∉ C ∧ Bornology.IsBounded (connectedComponentIn Cᶜ p)}).toReal
    let L := (eVariationOn γ (Icc (0 : ℝ) 1)).toReal
    4 * Real.pi * A ≤ L ^ 2 ∧
      (4 * Real.pi * A = L ^ 2 ↔
        ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ), 0 < r ∧ C = Metric.sphere c r) :=
  Isoperimetric.classical_isoperimetric γ hcontinuous hclosed hsimple hrectifiable

example (γ : ℝ → EuclideanSpace ℝ (Fin 2))
    (hcontinuous : ContinuousOn γ (Icc 0 1)) (hclosed : γ 0 = γ 1)
    (hsimple : InjOn γ (Ico 0 1)) (hrectifiable : BoundedVariationOn γ (Icc 0 1)) :
    let C := γ '' Icc (0 : ℝ) 1
    volume {p | p ∉ C ∧ Bornology.IsBounded (connectedComponentIn Cᶜ p)} ≠ ⊤ ∧
      eVariationOn γ (Icc (0 : ℝ) 1) ≠ ⊤ ∧
      0 < (eVariationOn γ (Icc (0 : ℝ) 1)).toReal := by
  let h : Isoperimetric.RectifiableJordan γ := ⟨hcontinuous, hclosed, hsimple, hrectifiable⟩
  exact ⟨h.volume_enclosed_ne_top, h.eVariationOn_ne_top, h.length_pos⟩

example (γ : ℝ → EuclideanSpace ℝ (Fin 2))
    (hcontinuous : ContinuousOn γ (Icc 0 1)) (hclosed : γ 0 = γ 1)
    (hsimple : InjOn γ (Ico 0 1)) (hrectifiable : BoundedVariationOn γ (Icc 0 1)) :
    MeasurableSet {p | p ∉ γ '' Icc (0 : ℝ) 1 ∧
      Bornology.IsBounded (connectedComponentIn (γ '' Icc (0 : ℝ) 1)ᶜ p)} :=
  (show Isoperimetric.RectifiableJordan γ from
    ⟨hcontinuous, hclosed, hsimple, hrectifiable⟩).measurableSet_enclosed

-- A positive-radius circle witnesses the four literal hypotheses and nonzero geometric area.
example (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (hr : 0 < r) :
    ∃ γ : ℝ → EuclideanSpace ℝ (Fin 2),
      ContinuousOn γ (Icc 0 1) ∧ γ 0 = γ 1 ∧ InjOn γ (Ico 0 1) ∧
      BoundedVariationOn γ (Icc 0 1) ∧ γ '' Icc (0 : ℝ) 1 = Metric.sphere c r ∧
      0 < (volume {p | p ∉ γ '' Icc (0 : ℝ) 1 ∧
        Bornology.IsBounded (connectedComponentIn (γ '' Icc (0 : ℝ) 1)ᶜ p)}).toReal := by
  let γ := Isoperimetric.circleParam c r
  have h := Isoperimetric.rectifiableJordan_circleParam c r hr
  refine ⟨γ, h.continuousOn, h.closed, h.injectiveOn, h.boundedVariationOn,
    Isoperimetric.trace_circleParam c r hr, ?_⟩
  change 0 < Isoperimetric.area γ
  rw [Isoperimetric.area_of_trace_sphere c r hr (Isoperimetric.trace_circleParam c r hr)]
  positivity
