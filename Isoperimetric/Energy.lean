import Isoperimetric.Parametrization

noncomputable section

open Set MeasureTheory

namespace Isoperimetric

variable {γ : ℝ → Plane}

theorem RectifiableJordan.integrableOn_deriv_arclengthParam (h : RectifiableJordan γ) :
    IntegrableOn (deriv (arclengthParam γ)) (Icc 0 1) :=
  integrableOn_deriv_of_lipschitzOn h.lipschitzOnWith_arclengthParam

theorem RectifiableJordan.integral_norm_deriv_arclengthParam (h : RectifiableJordan γ) :
    (∫ t in (0 : ℝ)..1, ‖deriv (arclengthParam γ) t‖) = length γ := by
  have hv := eVariationOn_eq_ofReal_integral_norm_deriv (by norm_num : (0 : ℝ) ≤ 1)
    h.lipschitzOnWith_arclengthParam
  have hi : 0 ≤ ∫ t in (0 : ℝ)..1, ‖deriv (arclengthParam γ) t‖ :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num) (fun _ ↦ norm_nonneg _)
  have hr := congrArg ENNReal.toReal hv
  rw [ENNReal.toReal_ofReal hi] at hr
  exact hr.symm.trans h.length_arclengthParam

/-- The variation parametrization has the geometric speed almost everywhere. -/
theorem RectifiableJordan.norm_deriv_arclengthParam_ae (h : RectifiableJordan γ) :
    ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      ‖deriv (arclengthParam γ) t‖ = length γ := by
  have hbound : (fun t ↦ ‖deriv (arclengthParam γ) t‖) ≤ᵐ[volume.restrict (Icc 0 1)]
      (fun _ ↦ length γ) := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact norm_deriv_le_of_lipschitzOn (Icc_mem_nhds ht.1 ht.2) h.lipschitzOnWith_arclengthParam
  apply (integral_eq_iff_of_ae_le h.integrableOn_deriv_arclengthParam.norm
    (integrable_const (length γ)) hbound).mp
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  rw [h.integral_norm_deriv_arclengthParam]
  simp

theorem RectifiableJordan.memLp_deriv_arclengthParam (h : RectifiableJordan γ) :
    MemLp (deriv (arclengthParam γ)) 2 (volume.restrict (Icc (0 : ℝ) 1)) := by
  exact MemLp.of_bound (aestronglyMeasurable_deriv _ _) (length γ)
    (h.norm_deriv_arclengthParam_ae.mono (fun _ ht ↦ ht.le))

theorem RectifiableJordan.absolutelyContinuousOnInterval_arclengthParam
    (h : RectifiableJordan γ) : AbsolutelyContinuousOnInterval (arclengthParam γ) 0 1 := by
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using h.lipschitzOnWith_arclengthParam

/-- The loop energy of the arclength parametrization is the squared geometric length. -/
theorem RectifiableJordan.energy_arclengthParam (h : RectifiableJordan γ) :
    (∫ t in (0 : ℝ)..1, ‖deriv (arclengthParam γ) t‖ ^ 2) = length γ ^ 2 := by
  rw [intervalIntegral.integral_of_le (by norm_num)]
  have heq : (fun t ↦ ‖deriv (arclengthParam γ) t‖ ^ 2) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun _ ↦ length γ ^ 2) := by
    rw [restrict_Ioc_eq_restrict_Icc]
    filter_upwards [h.norm_deriv_arclengthParam_ae] with t ht
    rw [ht]
  rw [integral_congr_ae heq]
  simp

end Isoperimetric
