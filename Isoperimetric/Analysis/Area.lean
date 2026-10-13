/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Isoperimetric.Analysis.Planar
import Isoperimetric.Analysis.Rotation

/-!
# Translation invariance of signed boundary area

The integral of each velocity coordinate vanishes for a closed loop. Consequently translating
the loop leaves its determinant integral unchanged. This identifies centered determinant
integrals with the signed determinant boundary functional.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Real Interval

namespace Isoperimetric

variable {η : ℝ → Plane}

/-- Each velocity coordinate integrates to zero because the loop is closed. -/
theorem ACLoop.integral_deriv_coordinate_eq_zero (h : ACLoop η)
    (i : Fin 2) : (∫ t in (0 : ℝ)..1, deriv η t i) = 0 := by
  have hac := h.absolutelyContinuous_coordinate i
  have heq : (∫ t in (0 : ℝ)..1, deriv η t i) =
      ∫ t in (0 : ℝ)..1, deriv (fun s ↦ η s i) t := by
    apply intervalIntegral.integral_congr_ae
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hd := h.deriv_coordinate_ae i
    rw [← restrict_Ioc_eq_restrict_Icc] at hd
    exact (ae_restrict_iff' measurableSet_Ioc).mp hd.symm
  rw [heq, hac.integral_deriv_eq_sub]
  rw [h.closed]
  simp

/-- Each coordinate of the velocity is interval-integrable. -/
theorem ACLoop.intervalIntegrable_deriv_coordinate (h : ACLoop η)
    (i : Fin 2) : IntervalIntegrable (fun t ↦ deriv η t i) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp h.integrableOn_deriv

/-- The determinant of the centered position and velocity is integrable. -/
theorem ACLoop.intervalIntegrable_determinant_centered (h : ACLoop η)
    (c : Plane) : IntervalIntegrable
      (fun t ↦ determinant (η t - c) (deriv η t)) volume 0 1 := by
  have hc (i : Fin 2) : ContinuousOn (fun t ↦ η t i - c i) (uIcc 0 1) := by
    have hac := h.absolutelyContinuous_coordinate i
    exact hac.continuousOn.sub continuousOn_const
  exact ((h.intervalIntegrable_deriv_coordinate 1).continuousOn_mul (hc 0)).sub
    ((h.intervalIntegrable_deriv_coordinate 0).continuousOn_mul (hc 1))

/-- Translating the loop does not change its signed boundary integral. -/
theorem ACLoop.signedArea_eq_centered_integral (h : ACLoop η) (c : Plane) :
    signedBoundaryArea η =
      (∫ t in (0 : ℝ)..1,
        determinant (η t - c) (deriv η t)) / 2 := by
  have hconst : IntervalIntegrable
      (fun t ↦ determinant c (deriv η t)) volume 0 1 :=
    ((h.intervalIntegrable_deriv_coordinate 1).const_mul (c 0)).sub
      ((h.intervalIntegrable_deriv_coordinate 0).const_mul (c 1))
  have hraw : IntervalIntegrable
      (fun t ↦ determinant (η t) (deriv η t)) volume 0 1 := by
    simpa using h.intervalIntegrable_determinant_centered 0
  have hz : (∫ t in (0 : ℝ)..1, determinant c (deriv η t)) = 0 := by
    simp only [determinant]
    rw [intervalIntegral.integral_sub
      ((h.intervalIntegrable_deriv_coordinate 1).const_mul (c 0))
      ((h.intervalIntegrable_deriv_coordinate 0).const_mul (c 1)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      h.integral_deriv_coordinate_eq_zero, h.integral_deriv_coordinate_eq_zero]
    simp
  unfold signedBoundaryArea
  simp_rw [determinant_sub_left]
  rw [intervalIntegral.integral_sub hraw hconst, hz, sub_zero]

end Isoperimetric
