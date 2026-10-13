import Isoperimetric.Arclength
import Mathlib.Analysis.ConstantSpeed

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory

namespace Isoperimetric

variable {γ : ℝ → Plane}

/-- The accumulated geometric length of the original, possibly non-AC parametrization. -/
def accumulatedLength (γ : ℝ → Plane) : ℝ → ℝ := variationOnFromTo γ (Icc 0 1) 0

@[simp] theorem accumulatedLength_zero (γ : ℝ → Plane) : accumulatedLength γ 0 = 0 :=
  variationOnFromTo.self γ (Icc 0 1) 0

@[simp] theorem accumulatedLength_one (γ : ℝ → Plane) : accumulatedLength γ 1 = length γ := by
  simp [accumulatedLength, variationOnFromTo.eq_of_le, length]

theorem RectifiableJordan.continuousOn_accumulatedLength (h : RectifiableJordan γ) :
    ContinuousOn (accumulatedLength γ) (Icc 0 1) := by
  intro t ht
  exact (h.boundedVariationOn.continuousWithinAt_variationOnFromTo_iff
    (by norm_num : (0 : ℝ) ∈ Icc 0 1) ht).mpr (h.continuousOn t ht)

theorem RectifiableJordan.accumulatedLength_image (h : RectifiableJordan γ) :
    accumulatedLength γ '' Icc 0 1 = Icc 0 (length γ) := by
  simpa using h.continuousOn_accumulatedLength.image_Icc_of_monotoneOn
    (by norm_num : (0 : ℝ) ≤ 1)
    (variationOnFromTo.monotoneOn h.boundedVariationOn.locallyBoundedVariationOn
      (by norm_num : (0 : ℝ) ∈ Icc 0 1))

/-- The natural parametrization on the interval of geometric lengths. -/
def unitSpeedParam (γ : ℝ → Plane) : ℝ → Plane := naturalParameterization γ (Icc 0 1) 0

theorem RectifiableJordan.unitSpeedParam_accumulatedLength (h : RectifiableJordan γ)
    {t : ℝ} (ht : t ∈ Icc 0 1) :
    unitSpeedParam γ (accumulatedLength γ t) = γ t := by
  exact edist_eq_zero.mp (edist_naturalParameterization_eq_zero
    h.boundedVariationOn.locallyBoundedVariationOn (by norm_num) ht)

theorem RectifiableJordan.hasUnitSpeed_unitSpeedParam (h : RectifiableJordan γ) :
    HasUnitSpeedOn (unitSpeedParam γ) (Icc 0 (length γ)) := by
  have hu := has_unit_speed_naturalParameterization γ
    h.boundedVariationOn.locallyBoundedVariationOn (by norm_num : (0 : ℝ) ∈ Icc 0 1)
  rw [← h.accumulatedLength_image]
  exact hu

/-- The normalized arclength loop on the original parameter interval. -/
def arclengthParam (γ : ℝ → Plane) (t : ℝ) : Plane := unitSpeedParam γ (length γ * t)

theorem RectifiableJordan.hasConstantSpeed_arclengthParam (h : RectifiableJordan γ) :
    HasConstantSpeedOnWith (arclengthParam γ) (Icc 0 1) ⟨length γ, h.length_pos.le⟩ := by
  let φ : ℝ → ℝ := fun t ↦ length γ * t
  have hmono : Monotone φ := fun _ _ hxy ↦ mul_le_mul_of_nonneg_left hxy h.length_pos.le
  have himage : φ '' Icc 0 1 = Icc 0 (length γ) := by
    simpa [φ] using (continuous_const.mul continuous_id).continuousOn.image_Icc_of_monotoneOn
      (by norm_num : (0 : ℝ) ≤ 1) (hmono.monotoneOn (Icc 0 1))
  intro x hx y hy
  change eVariationOn (unitSpeedParam γ ∘ φ) (Icc 0 1 ∩ Icc x y) = _
  rw [eVariationOn.comp_inter_Icc_eq_of_monotoneOn (unitSpeedParam γ) φ
    (hmono.monotoneOn _) hx hy, himage]
  have hxφ : φ x ∈ Icc 0 (length γ) := himage ▸ mem_image_of_mem φ hx
  have hyφ : φ y ∈ Icc 0 (length γ) := himage ▸ mem_image_of_mem φ hy
  rw [h.hasUnitSpeed_unitSpeedParam hxφ hyφ]
  apply congrArg ENNReal.ofReal
  with_unfolding_all change 1 * (length γ * y - length γ * x) = length γ * (y - x)
  ring

/-- Constant speed in the variation sense gives the required metric Lipschitz bound. -/
theorem lipschitzOnWith_of_hasConstantSpeed {f : ℝ → Plane} {a b : ℝ} {C : NNReal}
    (hf : HasConstantSpeedOnWith f (Icc a b) C) : LipschitzOnWith C f (Icc a b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  wlog hxy : x ≤ y generalizing x y
  · simpa only [dist_comm] using this y hy x hx (le_of_not_ge hxy)
  have hb := eVariationOn.edist_le f (s := Icc a b ∩ Icc x y)
    ⟨hx, le_rfl, hxy⟩ ⟨hy, hxy, le_rfl⟩
  rw [hf hx hy] at hb
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simp only [← dist_edist] at hr
  simpa [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hxy)] using hr

theorem RectifiableJordan.lipschitzOnWith_arclengthParam (h : RectifiableJordan γ) :
    LipschitzOnWith ⟨length γ, h.length_pos.le⟩ (arclengthParam γ) (Icc 0 1) :=
  lipschitzOnWith_of_hasConstantSpeed h.hasConstantSpeed_arclengthParam

/-- The normalized length coordinate, preserving the original orientation. -/
def normalizedLength (γ : ℝ → Plane) (t : ℝ) : ℝ := accumulatedLength γ t / length γ

theorem RectifiableJordan.normalizedLength_image (h : RectifiableJordan γ) :
    normalizedLength γ '' Icc 0 1 = Icc 0 1 := by
  have hc : ContinuousOn (normalizedLength γ) (Icc 0 1) :=
    h.continuousOn_accumulatedLength.div_const _
  have hm : MonotoneOn (normalizedLength γ) (Icc 0 1) := by
    intro s hs t ht hst
    exact div_le_div_of_nonneg_right
      (variationOnFromTo.monotoneOn h.boundedVariationOn.locallyBoundedVariationOn
        (by norm_num) hs ht hst) h.length_pos.le
  simpa [normalizedLength, h.length_pos.ne'] using
    hc.image_Icc_of_monotoneOn (by norm_num : (0 : ℝ) ≤ 1) hm

theorem RectifiableJordan.arclengthParam_normalizedLength (h : RectifiableJordan γ)
    {t : ℝ} (ht : t ∈ Icc 0 1) : arclengthParam γ (normalizedLength γ t) = γ t := by
  dsimp [arclengthParam, normalizedLength]
  rw [mul_div_cancel₀ _ h.length_pos.ne']
  exact h.unitSpeedParam_accumulatedLength ht

theorem RectifiableJordan.arclengthParam_isRectifiableJordan (h : RectifiableJordan γ) :
    RectifiableJordan (arclengthParam γ) := by
  have hzero : normalizedLength γ 0 = 0 := by simp [normalizedLength]
  have hone : normalizedLength γ 1 = 1 := by simp [normalizedLength, h.length_pos.ne']
  refine ⟨h.lipschitzOnWith_arclengthParam.continuousOn, ?_, ?_, ?_⟩
  · rw [← hzero, ← hone, h.arclengthParam_normalizedLength (by norm_num),
      h.arclengthParam_normalizedLength (by norm_num)]
    exact h.closed
  · intro s hs t ht heq
    obtain ⟨x, hx, hxs⟩ := h.normalizedLength_image.symm.subset (Ico_subset_Icc_self hs)
    obtain ⟨y, hy, hyt⟩ := h.normalizedLength_image.symm.subset (Ico_subset_Icc_self ht)
    have hxlt : x < 1 := lt_of_le_of_ne hx.2 (by
      intro hx1
      have : s = 1 := hxs.symm.trans (hx1 ▸ hone)
      exact hs.2.ne this)
    have hylt : y < 1 := lt_of_le_of_ne hy.2 (by
      intro hy1
      have : t = 1 := hyt.symm.trans (hy1 ▸ hone)
      exact ht.2.ne this)
    have hxy : γ x = γ y := by
      rw [← h.arclengthParam_normalizedLength hx, ← h.arclengthParam_normalizedLength hy,
        hxs, hyt]
      exact heq
    exact hxs.symm.trans ((congrArg (normalizedLength γ)
      (h.injectiveOn ⟨hx.1, hxlt⟩ ⟨hy.1, hylt⟩ hxy)).trans hyt)
  · simpa using h.hasConstantSpeed_arclengthParam.hasLocallyBoundedVariationOn
      0 1 (by norm_num) (by norm_num)

theorem RectifiableJordan.trace_arclengthParam (h : RectifiableJordan γ) :
    trace (arclengthParam γ) = trace γ := by
  apply Subset.antisymm
  · rintro p ⟨s, hs, hsp⟩
    obtain ⟨t, ht, hts⟩ := h.normalizedLength_image.symm.subset hs
    exact ⟨t, ht, (h.arclengthParam_normalizedLength ht).symm.trans (hts ▸ hsp)⟩
  · rintro p ⟨t, ht, htp⟩
    refine ⟨normalizedLength γ t, h.normalizedLength_image ▸ mem_image_of_mem _ ht, ?_⟩
    exact (h.arclengthParam_normalizedLength ht).trans htp

theorem RectifiableJordan.length_arclengthParam (h : RectifiableJordan γ) :
    length (arclengthParam γ) = length γ := by
  unfold length
  rw [← h.arclengthParam_isRectifiableJordan.hausdorffMeasure_trace,
    h.trace_arclengthParam, h.hausdorffMeasure_trace]

theorem RectifiableJordan.enclosed_arclengthParam (h : RectifiableJordan γ) :
    enclosed (arclengthParam γ) = enclosed γ := by
  unfold enclosed
  rw [h.trace_arclengthParam]

theorem RectifiableJordan.area_arclengthParam (h : RectifiableJordan γ) :
    area (arclengthParam γ) = area γ := by
  unfold area
  rw [h.enclosed_arclengthParam]

end Isoperimetric
