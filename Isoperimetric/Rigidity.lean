/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Isoperimetric.Analysis.CircularImage
import Isoperimetric.SignedArea

/-!
# Applying analytic rigidity to rectifiable Jordan loops

Arclength normalization supplies the independent AC-loop hypotheses. The signed Stieltjes
functional agrees with the determinant boundary functional; constant-speed energy is L².
These are the only bridges needed to apply the generic analytic circle theorem.
-/

noncomputable section

open Set MeasureTheory

namespace Isoperimetric

variable {γ : ℝ → Plane}

/-- Arclength normalization gives a closed AC loop with L² velocity. -/
theorem RectifiableJordan.arclengthParam_isACLoop (h : RectifiableJordan γ) :
    ACLoop (arclengthParam γ) :=
  ⟨h.absolutelyContinuousOnInterval_arclengthParam,
    h.arclengthParam_isRectifiableJordan.closed, h.memLp_deriv_arclengthParam⟩

/-- The signed Stieltjes area is a boundary integral using the vector derivative. -/
theorem RectifiableJordan.signedArea_eq_determinant_integral (h : RectifiableJordan γ) :
    MovingSofa.curveAreaFunctional h.arclengthParam_isRectifiableJordan.bvPath =
      (∫ t in (0 : ℝ)..1, determinant (arclengthParam γ t) (deriv (arclengthParam γ) t)) / 2 := by
  rw [h.signedArea_eq_coordinate_integral]
  apply congrArg (fun x : ℝ ↦ x / 2)
  apply intervalIntegral.integral_congr_ae
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have h0 := h.arclengthParam_isACLoop.deriv_coordinate_ae 0
  have h1 := h.arclengthParam_isACLoop.deriv_coordinate_ae 1
  rw [← restrict_Ioc_eq_restrict_Icc] at h0 h1
  apply (ae_restrict_iff' measurableSet_Ioc).mp
  filter_upwards [h0, h1] with t ht0 ht1
  simp only [determinant, ht0, ht1]

/-- Analytic rigidity applied to the constant-speed representative of a Jordan loop. -/
theorem RectifiableJordan.circle_of_signedArea_equality (h : RectifiableJordan γ)
    (ε : ℝ) (hε : ε ^ 2 = 1)
    (heq : length γ ^ 2 = 4 * Real.pi * ε *
      MovingSofa.curveAreaFunctional h.arclengthParam_isRectifiableJordan.bvPath) :
    ∃ (c : Plane) (r : ℝ), 0 < r ∧ trace γ = Metric.sphere c r := by
  have hne : ∃ t ∈ Icc (0 : ℝ) 1, arclengthParam γ t ≠ arclengthParam γ 0 := by
    refine ⟨1 / 2, by norm_num, ?_⟩
    intro heq
    have ht := h.arclengthParam_isRectifiableJordan.injectiveOn
      (by norm_num : (1 / 2 : ℝ) ∈ Ico 0 1) (by norm_num : (0 : ℝ) ∈ Ico 0 1) heq
    norm_num at ht
  have heq' : loopEnergy (arclengthParam γ) =
      4 * Real.pi * ε * signedBoundaryArea (arclengthParam γ) := by
    unfold loopEnergy signedBoundaryArea
    rw [← h.signedArea_eq_determinant_integral, h.energy_arclengthParam]
    exact heq
  obtain ⟨c, r, hr, himage⟩ :=
    h.arclengthParam_isACLoop.circle_of_signedArea_equality hne ε hε heq'
  exact ⟨c, r, hr, h.trace_arclengthParam.symm.trans himage⟩

end Isoperimetric
