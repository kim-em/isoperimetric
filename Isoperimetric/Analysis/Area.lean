import Isoperimetric.Analysis.Planar
import Isoperimetric.Analysis.Rotation
import Isoperimetric.SignedArea

noncomputable section

open Set MeasureTheory Filter
open scoped Real Interval

namespace Isoperimetric

variable {γ : ℝ → Plane}

theorem RectifiableJordan.integral_deriv_coordinate_eq_zero (h : RectifiableJordan γ)
    (i : Fin 2) : (∫ t in (0 : ℝ)..1, deriv (arclengthParam γ) t i) = 0 := by
  have hac : AbsolutelyContinuousOnInterval (fun t ↦ arclengthParam γ t i) 0 1 :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith.comp_absolutelyContinuousOnInterval
      h.absolutelyContinuousOnInterval_arclengthParam
  have heq : (∫ t in (0 : ℝ)..1, deriv (arclengthParam γ) t i) =
      ∫ t in (0 : ℝ)..1, deriv (fun s ↦ arclengthParam γ s i) t := by
    apply intervalIntegral.integral_congr_ae
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    have hd := deriv_coordinate_arclength_ae h i
    rw [← restrict_Ioc_eq_restrict_Icc] at hd
    exact (ae_restrict_iff' measurableSet_Ioc).mp hd.symm
  rw [heq, hac.integral_deriv_eq_sub]
  rw [h.arclengthParam_isRectifiableJordan.closed]
  simp

/-- The signed Stieltjes area is a boundary integral using the vector derivative. -/
theorem RectifiableJordan.signedArea_eq_determinant_integral (h : RectifiableJordan γ) :
    MovingSofa.curveAreaFunctional h.arclengthParam_isRectifiableJordan.bvPath =
      (∫ t in (0 : ℝ)..1, determinant (arclengthParam γ t) (deriv (arclengthParam γ) t)) / 2 := by
  rw [h.signedArea_eq_coordinate_integral]
  apply congrArg (fun x : ℝ ↦ x / 2)
  apply intervalIntegral.integral_congr_ae
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have h0 := deriv_coordinate_arclength_ae h 0
  have h1 := deriv_coordinate_arclength_ae h 1
  rw [← restrict_Ioc_eq_restrict_Icc] at h0 h1
  apply (ae_restrict_iff' measurableSet_Ioc).mp
  filter_upwards [h0, h1] with t ht0 ht1
  simp only [determinant, ht0, ht1]

theorem RectifiableJordan.intervalIntegrable_deriv_coordinate (h : RectifiableJordan γ)
    (i : Fin 2) : IntervalIntegrable (fun t ↦ deriv (arclengthParam γ) t i) volume 0 1 := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).integrable_comp h.integrableOn_deriv_arclengthParam

theorem RectifiableJordan.intervalIntegrable_determinant_centered (h : RectifiableJordan γ)
    (c : Plane) : IntervalIntegrable
      (fun t ↦ determinant (arclengthParam γ t - c) (deriv (arclengthParam γ) t)) volume 0 1 := by
  have hc (i : Fin 2) : ContinuousOn (fun t ↦ arclengthParam γ t i - c i) (uIcc 0 1) := by
    have hac : AbsolutelyContinuousOnInterval (fun t ↦ arclengthParam γ t i) 0 1 :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith.comp_absolutelyContinuousOnInterval
        h.absolutelyContinuousOnInterval_arclengthParam
    exact hac.continuousOn.sub continuousOn_const
  exact ((h.intervalIntegrable_deriv_coordinate 1).continuousOn_mul (hc 0)).sub
    ((h.intervalIntegrable_deriv_coordinate 0).continuousOn_mul (hc 1))

/-- Translating the loop does not change its signed boundary integral. -/
theorem RectifiableJordan.signedArea_eq_centered_integral (h : RectifiableJordan γ) (c : Plane) :
    MovingSofa.curveAreaFunctional h.arclengthParam_isRectifiableJordan.bvPath =
      (∫ t in (0 : ℝ)..1,
        determinant (arclengthParam γ t - c) (deriv (arclengthParam γ) t)) / 2 := by
  have hconst : IntervalIntegrable
      (fun t ↦ determinant c (deriv (arclengthParam γ) t)) volume 0 1 :=
    ((h.intervalIntegrable_deriv_coordinate 1).const_mul (c 0)).sub
      ((h.intervalIntegrable_deriv_coordinate 0).const_mul (c 1))
  have hraw : IntervalIntegrable
      (fun t ↦ determinant (arclengthParam γ t) (deriv (arclengthParam γ) t)) volume 0 1 := by
    simpa using h.intervalIntegrable_determinant_centered 0
  have hz : (∫ t in (0 : ℝ)..1, determinant c (deriv (arclengthParam γ) t)) = 0 := by
    simp only [determinant]
    rw [intervalIntegral.integral_sub
      ((h.intervalIntegrable_deriv_coordinate 1).const_mul (c 0))
      ((h.intervalIntegrable_deriv_coordinate 0).const_mul (c 1)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      h.integral_deriv_coordinate_eq_zero, h.integral_deriv_coordinate_eq_zero]
    simp
  rw [h.signedArea_eq_determinant_integral]
  simp_rw [determinant_sub_left]
  rw [intervalIntegral.integral_sub hraw hconst, hz, sub_zero]

end Isoperimetric
