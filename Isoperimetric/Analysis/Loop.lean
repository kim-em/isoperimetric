/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Isoperimetric.Analysis.Rotation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalAverage

/-!
# Absolutely continuous planar loops with finite energy

The analytic hypotheses used by rigidity are independent of Jordan geometry and arclength.
`ACLoop` requires only absolute continuity, equal endpoints and an L² velocity.
-/

noncomputable section

open Set MeasureTheory
open scoped Interval

namespace Isoperimetric

/-- A closed absolutely continuous planar loop with square-integrable velocity. -/
structure ACLoop (η : ℝ → Plane) : Prop where
  absolutelyContinuous : AbsolutelyContinuousOnInterval η 0 1
  closed : η 0 = η 1
  memLp_deriv : MemLp (deriv η) 2 (volume.restrict (Icc (0 : ℝ) 1))

/-- The mean position of a loop on the unit interval. -/
def loopMean (η : ℝ → Plane) : Plane := ⨍ t in (0 : ℝ)..1, η t

/-- The integral of squared speed on the unit interval. -/
def loopEnergy (η : ℝ → Plane) : ℝ := ∫ t in (0 : ℝ)..1, ‖deriv η t‖ ^ 2

/-- The signed determinant boundary functional, distinct from geometric enclosed area. -/
def signedBoundaryArea (η : ℝ → Plane) : ℝ :=
  (∫ t in (0 : ℝ)..1, determinant (η t) (deriv η t)) / 2

variable {η : ℝ → Plane}

/-- Each coordinate of an absolutely continuous loop is absolutely continuous. -/
theorem ACLoop.absolutelyContinuous_coordinate (h : ACLoop η) (i : Fin 2) :
    AbsolutelyContinuousOnInterval (fun t ↦ η t i) 0 1 :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith.comp_absolutelyContinuousOnInterval
    h.absolutelyContinuous

/-- A planar absolutely continuous loop is differentiable almost everywhere. -/
theorem ACLoop.ae_differentiableAt (h : ACLoop η) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), DifferentiableAt ℝ η t := by
  rw [ae_restrict_iff' measurableSet_Icc]
  simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
    h.absolutelyContinuous.boundedVariationOn.ae_differentiableAt_of_mem_uIcc

/-- An L² velocity is integrable on the finite unit interval. -/
theorem ACLoop.integrableOn_deriv (h : ACLoop η) : IntegrableOn (deriv η) (Icc 0 1) :=
  h.memLp_deriv.integrable (by norm_num)

end Isoperimetric
