/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Isoperimetric.Analysis.Area

/-!
# Equality forces a rotational ODE

Complete the square in the energy, centered moment and signed area of the loop.
Sharp Wirtinger makes both gaps nonnegative. At signed-area equality, the squared rotational
residual integrates to zero, so the circular ODE holds almost everywhere.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Real Interval

namespace Isoperimetric

variable {η : ℝ → Plane}

/-- Subtracting any fixed center gives a square-integrable loop. -/
theorem ACLoop.memLp_centered (h : ACLoop η) (c : Plane) :
    MemLp (fun t ↦ η t - c) 2 (volume.restrict (Icc (0 : ℝ) 1)) := by
  have hc : ContinuousOn (fun t ↦ η t - c) (Icc 0 1) := by
    rw [← uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact h.absolutelyContinuous.continuousOn.sub continuousOn_const
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact MemLp.of_bound (hc.aestronglyMeasurable measurableSet_Icc) C
    (ae_restrict_of_forall_mem measurableSet_Icc hC)

/-- The squared distance of the loop from any fixed center is integrable. -/
theorem ACLoop.intervalIntegrable_centered_norm_sq (h : ACLoop η)
    (c : Plane) : IntervalIntegrable (fun t ↦ ‖η t - c‖ ^ 2) volume 0 1 := by
  have hm := h.memLp_centered c
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm)

/-- The squared speed of the loop is integrable. -/
theorem ACLoop.intervalIntegrable_energy (h : ACLoop η) :
    IntervalIntegrable (fun t ↦ ‖deriv η t‖ ^ 2) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    ((memLp_two_iff_integrable_sq_norm h.memLp_deriv.aestronglyMeasurable).mp
      h.memLp_deriv)

/-- The squared rotational ODE residual is integrable for every center and angular speed. -/
theorem ACLoop.intervalIntegrable_rotationalResidual_sq (h : ACLoop η)
    (c : Plane) (ω : ℝ) : IntervalIntegrable
      (fun t ↦ ‖deriv η t - ω • quarterTurn (η t - c)‖ ^ 2)
      volume 0 1 := by
  have hj : MemLp (fun t ↦ quarterTurn (η t - c)) 2
      (volume.restrict (Icc (0 : ℝ) 1)) := quarterTurn.comp_memLp' (h.memLp_centered c)
  have hr : MemLp (fun t ↦ deriv η t -
      ω • quarterTurn (η t - c)) 2 (volume.restrict (Icc (0 : ℝ) 1)) :=
    h.memLp_deriv.sub (hj.const_smul ω)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    ((memLp_two_iff_integrable_sq_norm hr.aestronglyMeasurable).mp hr)

/-- Completion of squares for the signed area of the actual loop. -/
theorem ACLoop.complete_square (h : ACLoop η) (c : Plane) (ω : ℝ) :
    loopEnergy η - 2 * ω * signedBoundaryArea η =
      (1 / 2) * (∫ t in (0 : ℝ)..1,
        ‖deriv η t - ω • quarterTurn (η t - c)‖ ^ 2) +
      (1 / 2) * (loopEnergy η - ω ^ 2 * ∫ t in (0 : ℝ)..1, ‖η t - c‖ ^ 2) := by
  have hD : (∫ t in (0 : ℝ)..1,
      determinant (η t - c) (deriv η t)) =
      2 * signedBoundaryArea η := by
    linarith [h.signedArea_eq_centered_integral c]
  have hR : (∫ t in (0 : ℝ)..1,
      ‖deriv η t - ω • quarterTurn (η t - c)‖ ^ 2) =
      loopEnergy η + ω ^ 2 * (∫ t in (0 : ℝ)..1, ‖η t - c‖ ^ 2) -
      2 * ω * (∫ t in (0 : ℝ)..1,
        determinant (η t - c) (deriv η t)) := by
    simp_rw [norm_sub_quarterTurn_sq]
    rw [intervalIntegral.integral_sub
      (h.intervalIntegrable_energy.add
        ((h.intervalIntegrable_centered_norm_sq c).const_mul (ω ^ 2)))
      ((h.intervalIntegrable_determinant_centered c).const_mul (2 * ω)),
      intervalIntegral.integral_add h.intervalIntegrable_energy
        ((h.intervalIntegrable_centered_norm_sq c).const_mul (ω ^ 2)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rfl
  rw [hD] at hR
  rw [hR]
  ring

/-- Sharp Wirtinger bounds the centered moment by the loop energy. -/
theorem ACLoop.wirtinger_gap_nonneg (h : ACLoop η) :
    0 ≤ loopEnergy η - (2 * Real.pi) ^ 2 *
      ∫ t in (0 : ℝ)..1, ‖η t - loopMean η‖ ^ 2 := by
  have hw := h.wirtinger
  have hp : (2 * Real.pi) ^ 2 * (1 / (2 * Real.pi)) ^ 2 = 1 := by
    field_simp
  have hb := mul_le_mul_of_nonneg_left hw (sq_nonneg (2 * Real.pi))
  rw [← mul_assoc, hp, one_mul] at hb
  exact sub_nonneg.mpr hb

/-- At signed-area equality, the loop satisfies the circular ODE a.e.
The sign parameter accommodates either orientation. -/
theorem ACLoop.rotational_ode_of_signedArea_equality (h : ACLoop η)
    (ε : ℝ) (hε : ε ^ 2 = 1)
    (heq : loopEnergy η = 4 * Real.pi * ε *
      signedBoundaryArea η) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      deriv η t =
        (ε * (2 * Real.pi)) • quarterTurn (η t - loopMean η) := by
  let ω := ε * (2 * Real.pi)
  have hω : ω ^ 2 = (2 * Real.pi) ^ 2 := by dsimp [ω]; rw [mul_pow, hε, one_mul]
  have hzero : loopEnergy η - 2 * ω *
      signedBoundaryArea η = 0 := by
    dsimp [ω]
    rw [heq]
    ring
  have hRnonneg : 0 ≤ ∫ t in (0 : ℝ)..1,
      ‖deriv η t - ω • quarterTurn (η t - loopMean η)‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _ ↦ sq_nonneg _)
  have hidentity := h.complete_square (loopMean η) ω
  rw [hzero, hω] at hidentity
  have hRzero : (∫ t in (0 : ℝ)..1,
      ‖deriv η t - ω • quarterTurn (η t - loopMean η)‖ ^ 2) =
        0 := by
    linarith [h.wirtinger_gap_nonneg]
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae
    (by norm_num : (0 : ℝ) ≤ 1)
    (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))
    (h.intervalIntegrable_rotationalResidual_sq (loopMean η) ω)).mp hRzero
  rw [restrict_Ioc_eq_restrict_Icc] at hae
  filter_upwards [hae] with t ht
  have hz : ‖deriv η t - ω • quarterTurn (η t - loopMean η)‖
    = 0 :=
    (sq_eq_zero_iff).mp ht
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end Isoperimetric
