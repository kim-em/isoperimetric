import Isoperimetric.Energy
import Isoperimetric.Analysis.Wirtinger

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Real Interval

namespace Isoperimetric

variable {γ : ℝ → Plane}

theorem deriv_coordinate_arclength_ae (h : RectifiableJordan γ) (i : Fin 2) :
    (fun t ↦ deriv (fun s ↦ arclengthParam γ s i) t) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      (fun t ↦ deriv (arclengthParam γ) t i) := by
  have hd := h.lipschitzOnWith_arclengthParam.ae_differentiableWithinAt
    (μ := volume) measurableSet_Icc
  rw [← restrict_Ioo_eq_restrict_Icc] at hd ⊢
  filter_upwards [hd, ae_restrict_mem measurableSet_Ioo] with t ht hto
  have hdAt := ht.differentiableAt (Icc_mem_nhds hto.1 hto.2)
  exact ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt t hdAt.hasDerivAt).deriv

theorem wirtinger_arclength (h : RectifiableJordan γ) :
    (∫ t in (0 : ℝ)..1, ‖arclengthParam γ t - ⨍ s in (0 : ℝ)..1, arclengthParam γ s‖ ^ 2) ≤
      (1 / (2 * Real.pi)) ^ 2 * length γ ^ 2 := by
  let η := arclengthParam γ
  let c := ⨍ s in (0 : ℝ)..1, η s
  let k := (1 / (2 * Real.pi)) ^ 2
  have hηint : IntervalIntegrable η volume 0 1 :=
    (show ContinuousOn η (uIcc 0 1) by
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        h.lipschitzOnWith_arclengthParam.continuousOn).intervalIntegrable
  have hac (i : Fin 2) : AbsolutelyContinuousOnInterval (fun t ↦ η t i) 0 1 :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith.comp_absolutelyContinuousOnInterval
      h.absolutelyContinuousOnInterval_arclengthParam
  have hlp (i : Fin 2) : MemLp (fun t ↦ deriv (fun s ↦ η s i) t) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    rw [restrict_Ioc_eq_restrict_Icc]
    have hp : MemLp (fun t ↦ deriv (arclengthParam γ) t i) 2
        (volume.restrict (Icc (0 : ℝ) 1)) :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' h.memLp_deriv_arclengthParam
    exact hp.ae_eq (deriv_coordinate_arclength_ae h i).symm
  have hmean (i : Fin 2) : (⨍ t in (0 : ℝ)..1, η t i) = c i := by
    change (⨍ t in (0 : ℝ)..1, (EuclideanSpace.proj (𝕜 := ℝ) i) (η t)) =
      (EuclideanSpace.proj (𝕜 := ℝ) i) c
    dsimp [c]
    simp only [interval_average_eq, sub_zero, inv_one, one_smul]
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).intervalIntegral_comp_comm
      hηint
  have hdev (i : Fin 2) : IntervalIntegrable (fun t ↦ (η t i - c i) ^ 2) volume 0 1 :=
    (((hac i).continuousOn.sub continuousOn_const).pow 2).intervalIntegrable
  have hdint (i : Fin 2) : IntervalIntegrable (fun t ↦ deriv η t i ^ 2) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr
    exact ((EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' h.memLp_deriv_arclengthParam).integrable_sq
  have hscalar (i : Fin 2) : (∫ t in (0 : ℝ)..1, (η t i - c i) ^ 2) ≤
      k * ∫ t in (0 : ℝ)..1, deriv η t i ^ 2 := by
    have hs := wirtinger_real (by norm_num : (0 : ℝ) < 1) (hac i)
      (congrArg (fun z : Plane ↦ z i) h.arclengthParam_isRectifiableJordan.closed) (hlp i)
    simp only [hmean i, Real.norm_eq_abs, sq_abs, sub_zero] at hs
    have hdintEq : (∫ t in (0 : ℝ)..1, deriv (fun s ↦ η s i) t ^ 2) =
        ∫ t in (0 : ℝ)..1, deriv η t i ^ 2 := by
      apply intervalIntegral.integral_congr_ae
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      have heq := deriv_coordinate_arclength_ae h i
      rw [← restrict_Ioc_eq_restrict_Icc] at heq
      exact (ae_restrict_iff' measurableSet_Ioc).mp (heq.mono (fun _ ht ↦ congrArg (fun x : ℝ ↦ x ^ 2) ht))
    rw [hdintEq] at hs
    exact hs
  calc
    _ = (∫ t in (0 : ℝ)..1, (η t 0 - c 0) ^ 2) +
        ∫ t in (0 : ℝ)..1, (η t 1 - c 1) ^ 2 := by
      simp_rw [MovingSofa.Point.norm_sq_eq, PiLp.sub_apply]
      exact intervalIntegral.integral_add (hdev 0) (hdev 1)
    _ ≤ k * (∫ t in (0 : ℝ)..1, deriv η t 0 ^ 2) +
        k * ∫ t in (0 : ℝ)..1, deriv η t 1 ^ 2 := add_le_add (hscalar 0) (hscalar 1)
    _ = k * (∫ t in (0 : ℝ)..1, ‖deriv η t‖ ^ 2) := by
      rw [← mul_add, ← intervalIntegral.integral_add (hdint 0) (hdint 1)]
      simp_rw [MovingSofa.Point.norm_sq_eq]
    _ = _ := by rw [h.energy_arclengthParam]

end Isoperimetric
