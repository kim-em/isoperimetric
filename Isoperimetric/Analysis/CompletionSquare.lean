import Isoperimetric.Analysis.Area

noncomputable section

open Set MeasureTheory Filter
open scoped Real Interval

namespace Isoperimetric

variable {γ : ℝ → Plane}

/-- The mean of the arclength loop. -/
def arclengthMean (γ : ℝ → Plane) : Plane := ⨍ t in (0 : ℝ)..1, arclengthParam γ t

theorem RectifiableJordan.memLp_centered_arclength (h : RectifiableJordan γ) (c : Plane) :
    MemLp (fun t ↦ arclengthParam γ t - c) 2 (volume.restrict (Icc (0 : ℝ) 1)) := by
  have hc : ContinuousOn (fun t ↦ arclengthParam γ t - c) (Icc 0 1) := by
    rw [← uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    with_unfolding_all exact
      h.absolutelyContinuousOnInterval_arclengthParam.continuousOn.sub continuousOn_const
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact MemLp.of_bound (hc.aestronglyMeasurable measurableSet_Icc) C
    (ae_restrict_of_forall_mem measurableSet_Icc hC)

theorem RectifiableJordan.intervalIntegrable_centered_norm_sq (h : RectifiableJordan γ)
    (c : Plane) : IntervalIntegrable (fun t ↦ ‖arclengthParam γ t - c‖ ^ 2) volume 0 1 := by
  have hm := h.memLp_centered_arclength c
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm)

theorem RectifiableJordan.intervalIntegrable_energy (h : RectifiableJordan γ) :
    IntervalIntegrable (fun t ↦ ‖deriv (arclengthParam γ) t‖ ^ 2) volume 0 1 :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    ((memLp_two_iff_integrable_sq_norm h.memLp_deriv_arclengthParam.aestronglyMeasurable).mp
      h.memLp_deriv_arclengthParam)

theorem RectifiableJordan.intervalIntegrable_rotationalResidual_sq (h : RectifiableJordan γ)
    (c : Plane) (ω : ℝ) : IntervalIntegrable
      (fun t ↦ ‖deriv (arclengthParam γ) t - ω • quarterTurn (arclengthParam γ t - c)‖ ^ 2)
      volume 0 1 := by
  have hj : MemLp (fun t ↦ quarterTurn (arclengthParam γ t - c)) 2
      (volume.restrict (Icc (0 : ℝ) 1)) := quarterTurn.comp_memLp' (h.memLp_centered_arclength c)
  have hr : MemLp (fun t ↦ deriv (arclengthParam γ) t -
      ω • quarterTurn (arclengthParam γ t - c)) 2 (volume.restrict (Icc (0 : ℝ) 1)) :=
    h.memLp_deriv_arclengthParam.sub (hj.const_smul ω)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
    ((memLp_two_iff_integrable_sq_norm hr.aestronglyMeasurable).mp hr)

/-- Completion of squares for the signed area of the actual arclength loop. -/
theorem RectifiableJordan.completeSquare (h : RectifiableJordan γ) (c : Plane) (ω : ℝ) :
    length γ ^ 2 - 2 * ω * MovingSofa.curveAreaFunctional h.arclengthParam_isRectifiableJordan.bvPath =
      (1 / 2) * (∫ t in (0 : ℝ)..1,
        ‖deriv (arclengthParam γ) t - ω • quarterTurn (arclengthParam γ t - c)‖ ^ 2) +
      (1 / 2) * (length γ ^ 2 - ω ^ 2 * ∫ t in (0 : ℝ)..1, ‖arclengthParam γ t - c‖ ^ 2) := by
  have hD : (∫ t in (0 : ℝ)..1,
      determinant (arclengthParam γ t - c) (deriv (arclengthParam γ) t)) =
      2 * MovingSofa.curveAreaFunctional h.arclengthParam_isRectifiableJordan.bvPath := by
    linarith [h.signedArea_eq_centered_integral c]
  have hR : (∫ t in (0 : ℝ)..1,
      ‖deriv (arclengthParam γ) t - ω • quarterTurn (arclengthParam γ t - c)‖ ^ 2) =
      length γ ^ 2 + ω ^ 2 * (∫ t in (0 : ℝ)..1, ‖arclengthParam γ t - c‖ ^ 2) -
      2 * ω * (∫ t in (0 : ℝ)..1,
        determinant (arclengthParam γ t - c) (deriv (arclengthParam γ) t)) := by
    simp_rw [norm_sub_quarterTurn_sq]
    rw [intervalIntegral.integral_sub
      (h.intervalIntegrable_energy.add ((h.intervalIntegrable_centered_norm_sq c).const_mul (ω ^ 2)))
      ((h.intervalIntegrable_determinant_centered c).const_mul (2 * ω)),
      intervalIntegral.integral_add h.intervalIntegrable_energy
        ((h.intervalIntegrable_centered_norm_sq c).const_mul (ω ^ 2)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      h.energy_arclengthParam]
  rw [hD] at hR
  rw [hR]
  ring

theorem RectifiableJordan.wirtinger_gap_nonneg (h : RectifiableJordan γ) :
    0 ≤ length γ ^ 2 - (2 * Real.pi) ^ 2 *
      ∫ t in (0 : ℝ)..1, ‖arclengthParam γ t - arclengthMean γ‖ ^ 2 := by
  have hw := wirtinger_arclength h
  have hp : (2 * Real.pi) ^ 2 * (1 / (2 * Real.pi)) ^ 2 = 1 := by
    field_simp
  have hb := mul_le_mul_of_nonneg_left hw (sq_nonneg (2 * Real.pi))
  rw [← mul_assoc, hp, one_mul] at hb
  exact sub_nonneg.mpr hb

/-- At signed-area equality, the arclength loop satisfies the circular ODE a.e.
The sign parameter accommodates either orientation. -/
theorem RectifiableJordan.rotational_ode_of_signedArea_equality (h : RectifiableJordan γ)
    (ε : ℝ) (hε : ε ^ 2 = 1)
    (heq : length γ ^ 2 = 4 * Real.pi * ε *
      MovingSofa.curveAreaFunctional h.arclengthParam_isRectifiableJordan.bvPath) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      deriv (arclengthParam γ) t =
        (ε * (2 * Real.pi)) • quarterTurn (arclengthParam γ t - arclengthMean γ) := by
  let ω := ε * (2 * Real.pi)
  have hω : ω ^ 2 = (2 * Real.pi) ^ 2 := by dsimp [ω]; rw [mul_pow, hε, one_mul]
  have hzero : length γ ^ 2 - 2 * ω *
      MovingSofa.curveAreaFunctional h.arclengthParam_isRectifiableJordan.bvPath = 0 := by
    dsimp [ω]
    rw [heq]
    ring
  have hRnonneg : 0 ≤ ∫ t in (0 : ℝ)..1,
      ‖deriv (arclengthParam γ) t - ω • quarterTurn (arclengthParam γ t - arclengthMean γ)‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _ ↦ sq_nonneg _)
  have hidentity := h.completeSquare (arclengthMean γ) ω
  rw [hzero, hω] at hidentity
  have hRzero : (∫ t in (0 : ℝ)..1,
      ‖deriv (arclengthParam γ) t - ω • quarterTurn (arclengthParam γ t - arclengthMean γ)‖ ^ 2) = 0 := by
    linarith [h.wirtinger_gap_nonneg]
  have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae
    (by norm_num : (0 : ℝ) ≤ 1)
    (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))
    (h.intervalIntegrable_rotationalResidual_sq (arclengthMean γ) ω)).mp hRzero
  rw [restrict_Ioc_eq_restrict_Icc] at hae
  filter_upwards [hae] with t ht
  have hz : ‖deriv (arclengthParam γ) t - ω • quarterTurn (arclengthParam γ t - arclengthMean γ)‖ = 0 :=
    (sq_eq_zero_iff).mp ht
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

end Isoperimetric
