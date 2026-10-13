import Isoperimetric.CircleInterior
import Isoperimetric.Analysis.CircularImage
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Set MeasureTheory Complex
open scoped Real Interval

namespace Isoperimetric

/-- The usual counterclockwise once-traversal of a circle on the unit interval. -/
def circleParam (c : Plane) (r t : ℝ) : Plane :=
  c + r • planeComplex.symm (Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * I))

theorem hasDerivAt_circleParam (c : Plane) (r t : ℝ) :
    HasDerivAt (circleParam c r)
      (r • planeComplex.symm (((2 * Real.pi : ℝ) : ℂ) * I *
        Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * I))) t := by
  have hi : HasDerivAt (fun s : ℝ ↦ ((2 * Real.pi * s : ℝ) : ℂ) * I)
      (((2 * Real.pi : ℝ) : ℂ) * I) t := by
    convert (ofRealCLM.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).const_mul (2 * Real.pi))).mul_const I using 1
    · funext s
      simp [Function.comp_apply, mul_comm]
    · simp
  have he : HasDerivAt (fun s : ℝ ↦ Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * I))
      (((2 * Real.pi : ℝ) : ℂ) * I * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * I)) t := by
    simpa only [mul_comm] using hi.cexp
  exact ((planeComplex.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t he).const_smul r).const_add c

theorem norm_deriv_circleParam (c : Plane) (r : ℝ) (hr : 0 < r) (t : ℝ) :
    ‖deriv (circleParam c r) t‖ = 2 * Real.pi * r := by
  rw [(hasDerivAt_circleParam c r t).deriv, norm_smul, planeComplex.symm.norm_map]
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs r, Real.norm_eq_abs (2 * Real.pi), abs_of_pos hr,
    abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  ring

theorem lipschitzWith_circleParam (c : Plane) (r : ℝ) (hr : 0 < r) :
    LipschitzWith ⟨2 * Real.pi * r, by positivity⟩ (circleParam c r) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t ↦ (hasDerivAt_circleParam c r t).differentiableAt)
  intro t
  -- Normalize the NNReal coefficient and the EuclideanSpace norm instances.
  with_unfolding_all exact_mod_cast (norm_deriv_circleParam c r hr t).le

theorem trace_circleParam (c : Plane) (r : ℝ) (hr : 0 < r) :
    trace (circleParam c r) = Metric.sphere c r := by
  have hfull := exp_fullTurn_image 1 (by norm_num)
  simp only [one_mul] at hfull
  apply Subset.antisymm
  · rintro p ⟨t, _, rfl⟩
    rw [Metric.mem_sphere, dist_eq_norm]
    rw [circleParam, add_sub_cancel_left, norm_smul, planeComplex.symm.norm_map,
      Complex.norm_exp_ofReal_mul_I, Real.norm_eq_abs, abs_of_pos hr, mul_one]
  · intro p hp
    have hp0 : ‖p - c‖ = r := by simpa [Metric.mem_sphere, dist_eq_norm] using hp
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hu : planeComplex (p - c) / (r : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_div, planeComplex.norm_map,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hp0, div_self hr.ne']
    obtain ⟨t, ht, htu⟩ := hfull.symm.subset hu
    dsimp only at htu
    refine ⟨t, ht, ?_⟩
    have hdiff : circleParam c r t - c = p - c := by
      apply planeComplex.injective
      rw [circleParam, add_sub_cancel_left, planeComplex.map_smul,
        planeComplex.apply_symm_apply, htu]
      simpa only [Complex.real_smul] using mul_div_cancel₀ (planeComplex (p - c)) hrC
    exact sub_left_inj.mp hdiff

theorem rectifiableJordan_circleParam (c : Plane) (r : ℝ) (hr : 0 < r) :
    RectifiableJordan (circleParam c r) := by
  have hlip := lipschitzWith_circleParam c r hr
  refine ⟨hlip.continuous.continuousOn, ?_, ?_, ?_⟩
  · simp [circleParam, Complex.ofReal_mul, Complex.exp_two_pi_mul_I]
  · intro s hs t ht hst
    have he : planeComplex.symm (Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * I)) =
        planeComplex.symm (Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * I)) := by
      have he := congrArg (fun z : Plane ↦ r⁻¹ • (z - c)) hst
      simpa only [circleParam, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using he
    have heC := planeComplex.symm.injective he
    have heCircle : Circle.exp (2 * Real.pi * s) = Circle.exp (2 * Real.pi * t) :=
      Subtype.ext heC
    have hs0 : 2 * Real.pi * s ∈ Ico 0 (2 * Real.pi) :=
      ⟨mul_nonneg (by positivity) hs.1,
        by simpa only [mul_one] using mul_lt_mul_of_pos_left hs.2 (by positivity : 0 < 2 * Real.pi)⟩
    have ht0 : 2 * Real.pi * t ∈ Ico 0 (2 * Real.pi) :=
      ⟨mul_nonneg (by positivity) ht.1,
        by simpa only [mul_one] using mul_lt_mul_of_pos_left ht.2 (by positivity : 0 < 2 * Real.pi)⟩
    have heAngle := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi)
      (by simp) hs0 ht0 heCircle
    exact mul_left_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) heAngle
  · have hid : BoundedVariationOn (id : ℝ → ℝ) (Icc 0 1) := by
      rw [BoundedVariationOn, eVariationOn_id_Icc]
      exact ENNReal.ofReal_ne_top
    exact hlip.comp_boundedVariationOn hid

theorem length_circleParam (c : Plane) (r : ℝ) (hr : 0 < r) :
    length (circleParam c r) = 2 * Real.pi * r := by
  have hv := eVariationOn_eq_ofReal_integral_norm_deriv (by norm_num : (0 : ℝ) ≤ 1)
    (lipschitzWith_circleParam c r hr).lipschitzOnWith
  simp_rw [norm_deriv_circleParam c r hr] at hv
  simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hv
  rw [length, hv, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi * r)]

/-- Every permitted parametrization of a circle has its usual geometric circumference. -/
theorem RectifiableJordan.length_of_trace_sphere {γ : ℝ → Plane} (h : RectifiableJordan γ)
    (c : Plane) (r : ℝ) (hr : 0 < r) (htrace : trace γ = Metric.sphere c r) :
    length γ = 2 * Real.pi * r := by
  have hc := rectifiableJordan_circleParam c r hr
  unfold length
  rw [← h.hausdorffMeasure_trace, htrace, ← trace_circleParam c r hr, hc.hausdorffMeasure_trace]
  exact length_circleParam c r hr

/-- The circle converse uses actual enclosed Lebesgue area and total variation length. -/
theorem RectifiableJordan.equality_of_circle {γ : ℝ → Plane} (h : RectifiableJordan γ)
    (c : Plane) (r : ℝ) (hr : 0 < r) (htrace : trace γ = Metric.sphere c r) :
    4 * Real.pi * area γ = length γ ^ 2 := by
  rw [area_of_trace_sphere c r hr htrace, h.length_of_trace_sphere c r hr htrace]
  ring

end Isoperimetric
