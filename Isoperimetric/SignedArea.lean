import Isoperimetric.Parametrization
import Isoperimetric.Energy
import Isoperimetric.StieltjesDensity
import MovingSofa.Curve.AreaTransport
import MovingSofa.Analysis.Stieltjes.DensityIntegration

noncomputable section

open Set MeasureTheory

namespace Isoperimetric

variable {γ : ℝ → Plane}

/-- The interval-subtype BV path used by MovingSofa's Stieltjes area functional. -/
def RectifiableJordan.bvPath (h : RectifiableJordan γ) : MovingSofa.ContinuousBVPaths 0 1 := by
  have hb : BoundedVariationOn (fun t : Icc (0 : ℝ) 1 ↦ γ t) univ :=
    ne_top_of_le_ne_top h.boundedVariationOn (eVariationOn.comp_le_of_monotoneOn γ
      Subtype.val (fun _ _ _ _ hst ↦ hst) (fun t _ ↦ t.property))
  refine ⟨fun t ↦ γ t, continuousOn_iff_continuous_domRestrict.mp h.continuousOn, ?_⟩
  intro i
  exact (EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith.comp_boundedVariationOn hb

theorem RectifiableJordan.monotoneOn_normalizedLength (h : RectifiableJordan γ) :
    MonotoneOn (normalizedLength γ) (Icc 0 1) := by
  intro s hs t ht hst
  exact div_le_div_of_nonneg_right
    (variationOnFromTo.monotoneOn h.boundedVariationOn.locallyBoundedVariationOn
      (by norm_num) hs ht hst) h.length_pos.le

/-- Arclength reparametrization also preserves the signed Stieltjes area.
This is a separate bridge; Lebesgue area remains the geometric `area` definition. -/
theorem RectifiableJordan.signedArea_arclengthParam (h : RectifiableJordan γ) :
    MovingSofa.curveAreaFunctional h.arclengthParam_isRectifiableJordan.bvPath =
      MovingSofa.curveAreaFunctional h.bvPath := by
  let φ : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun t ↦
    ⟨normalizedLength γ t, h.normalizedLength_image.subset (mem_image_of_mem _ t.property)⟩
  have hc : Continuous φ := by
    apply Continuous.subtype_mk
    exact continuousOn_iff_continuous_domRestrict.mp
      (h.continuousOn_accumulatedLength.div_const _)
  have hm : Monotone φ := fun s t hst ↦
    h.monotoneOn_normalizedLength s.property t.property hst
  have hs : Function.Surjective φ := by
    intro t
    obtain ⟨s, hs, hst⟩ := h.normalizedLength_image.symm.subset t.property
    exact ⟨⟨s, hs⟩, Subtype.ext hst⟩
  symm
  apply MovingSofa.curveAreaFunctional_eq_of_comp_monotone_surjective
    (by norm_num) (by norm_num) h.arclengthParam_isRectifiableJordan.bvPath h.bvPath φ hc hm hs
  funext t
  exact (h.arclengthParam_normalizedLength t.property).symm

theorem RectifiableJordan.stieltjes_coordinate_arclengthParam (h : RectifiableJordan γ)
    (i j : Fin 2) :
    MovingSofa.intervalStieltjesIntegral
      (MovingSofa.continuousBVCoordinate h.arclengthParam_isRectifiableJordan.bvPath i)
      (fun t ↦ arclengthParam γ t j) univ =
      ∫ t in (0 : ℝ)..1, arclengthParam γ t j * deriv (fun s ↦ arclengthParam γ s i) t := by
  have hac : AbsolutelyContinuousOnInterval (fun t ↦ arclengthParam γ t i) 0 1 :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith.comp_absolutelyContinuousOnInterval
      h.absolutelyContinuousOnInterval_arclengthParam
  have hd := hasIntervalStieltjesDensity_of_absolutelyContinuous (by norm_num)
    (MovingSofa.continuousBVCoordinate h.arclengthParam_isRectifiableJordan.bvPath i)
    (fun t ↦ arclengthParam γ t i) (fun _ ↦ rfl) hac
  have hq : Continuous (fun t : Icc (0 : ℝ) 1 ↦ arclengthParam γ t j) :=
    (PiLp.continuous_apply 2 _ j).comp
      h.arclengthParam_isRectifiableJordan.bvPath.property.1
  rw [MovingSofa.intervalStieltjesIntegral_eq_integral_mul_of_density _ hd
    hq univ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  have hsub := integral_subtype_comap (μ := volume) (s := Icc (0 : ℝ) 1) measurableSet_Icc
    (f := fun t : ℝ ↦ arclengthParam γ t j * deriv (fun s ↦ arclengthParam γ s i) t)
  calc
    _ = ∫ t in Icc (0 : ℝ) 1,
        arclengthParam γ t j * deriv (fun s ↦ arclengthParam γ s i) t := hsub
    _ = _ := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- The signed Stieltjes area has its usual boundary integral formula for the
Lipschitz arclength loop, using the almost-everywhere coordinate derivatives. -/
theorem RectifiableJordan.signedArea_eq_coordinate_integral (h : RectifiableJordan γ) :
    MovingSofa.curveAreaFunctional h.arclengthParam_isRectifiableJordan.bvPath =
      (∫ t in (0 : ℝ)..1,
        arclengthParam γ t 0 * deriv (fun s ↦ arclengthParam γ s 1) t -
        arclengthParam γ t 1 * deriv (fun s ↦ arclengthParam γ s 0) t) / 2 := by
  have hac (i : Fin 2) : AbsolutelyContinuousOnInterval (fun t ↦ arclengthParam γ t i) 0 1 :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).lipschitzWith.comp_absolutelyContinuousOnInterval
      h.absolutelyContinuousOnInterval_arclengthParam
  have hint (i j : Fin 2) : IntervalIntegrable
      (fun t ↦ arclengthParam γ t j * deriv (fun s ↦ arclengthParam γ s i) t) volume 0 1 :=
    (hac i).intervalIntegrable_deriv.continuousOn_mul (hac j).continuousOn
  unfold MovingSofa.curveAreaFunctional
  change (MovingSofa.intervalStieltjesIntegral
      (MovingSofa.continuousBVCoordinate h.arclengthParam_isRectifiableJordan.bvPath 1)
      (fun t ↦ arclengthParam γ t 0) univ -
    MovingSofa.intervalStieltjesIntegral
      (MovingSofa.continuousBVCoordinate h.arclengthParam_isRectifiableJordan.bvPath 0)
      (fun t ↦ arclengthParam γ t 1) univ) / 2 = _
  rw [h.stieltjes_coordinate_arclengthParam 1 0,
    h.stieltjes_coordinate_arclengthParam 0 1, intervalIntegral.integral_sub (hint 1 0) (hint 0 1)]

end Isoperimetric
