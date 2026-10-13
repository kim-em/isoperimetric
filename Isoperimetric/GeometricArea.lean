import Isoperimetric.Analysis.CircularImage
import Isoperimetric.Circle
import MovingSofa.Curve.Jordan.SignedArea

noncomputable section

open Set MeasureTheory

namespace Isoperimetric

variable {γ : ℝ → Plane}

theorem RectifiableJordan.range_bvPath (h : RectifiableJordan γ) :
    range h.bvPath.val = trace γ := by
  ext p
  constructor
  · rintro ⟨t, htp⟩
    exact ⟨t, t.property, htp⟩
  · rintro ⟨t, ht, htp⟩
    exact ⟨⟨t, ht⟩, htp⟩

/-- The existing Jordan area theorem applies to the original BV parametrization,
once its winding orientation has been established. -/
theorem RectifiableJordan.signedArea_eq_area_of_counterclockwise (h : RectifiableJordan γ)
    (hori : MovingSofa.IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1)
      (trace γ) true h.bvPath.val) :
    MovingSofa.curveAreaFunctional h.bvPath = area γ := by
  exact MovingSofa.curveArea_eq_jordanInterior_area 0 1 (by norm_num) (trace γ) h.bvPath hori

/-- Reverse a clockwise once-traversal and reuse the positive orientation area theorem. -/
theorem RectifiableJordan.signedArea_eq_neg_area_of_clockwise (h : RectifiableJordan γ)
    (hori : MovingSofa.IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1)
      (trace γ) false h.bvPath.val) :
    MovingSofa.curveAreaFunctional h.bvPath = -area γ := by
  let φ := Set.Icc.reverse (by norm_num : (0 : ℝ) ≤ 1)
  have hφ0 : φ ⟨0, by norm_num⟩ = ⟨1, by norm_num⟩ := by
    apply Subtype.ext
    simp [φ, Set.Icc.reverse]
  have hφ1 : φ ⟨1, by norm_num⟩ = ⟨0, by norm_num⟩ := by
    apply Subtype.ext
    simp [φ, Set.Icc.reverse]
  have hφc := Set.Icc.continuous_reverse (by norm_num : (0 : ℝ) ≤ 1)
  have hφs := Set.Icc.surjective_reverse (by norm_num : (0 : ℝ) ≤ 1)
  obtain ⟨y, hy, hya⟩ := MovingSofa.curveArea_comp_antitone_surjective
    (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) h.bvPath φ hφc
    (Set.Icc.antitone_reverse (by norm_num : (0 : ℝ) ≤ 1)) hφs
  have hyr : range y.val = trace γ := by
    rw [hy, range_comp, hφs.range_eq, image_univ, h.range_bvPath]
  have hyclosed : y.val ⟨0, by norm_num⟩ = y.val ⟨1, by norm_num⟩ := by
    rw [hy, Function.comp_apply, Function.comp_apply, hφ0, hφ1]
    exact h.closed.symm
  have hyinj : InjOn y.val {t | (t : ℝ) < 1} := by
    intro s hs t ht heq
    rw [hy] at heq
    have hγeq : γ (φ s) = γ (φ t) := heq
    rcases h.eq_or_endpoints (φ s).property (φ t).property hγeq with he | ⟨hs0, _⟩ | ⟨_, ht0⟩
    · apply Subtype.ext
      simp only [φ, Set.Icc.reverse, zero_add] at he
      linarith
    · simp only [φ, Set.Icc.reverse, zero_add] at hs0
      have hslt : (s : ℝ) < 1 := hs
      linarith
    · simp only [φ, Set.Icc.reverse, zero_add] at ht0
      have htlt : (t : ℝ) < 1 := ht
      linarith
  have hyori : MovingSofa.IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1)
      (trace γ) true y.val := by
    refine ⟨by norm_num, h.isJordanCurve, y.property.1, hyr, hyclosed, hyinj, ?_⟩
    intro p hp
    have hw : MovingSofa.curveWinding (by norm_num : (0 : ℝ) ≤ 1) h.bvPath.val p = -1 := by
      exact hori.2.2.2.2.2.2 p hp
    obtain ⟨θ, hθ⟩ := MovingSofa.exists_curveAngleLift_of_curveWinding_ne_zero
      (by norm_num : (0 : ℝ) ≤ 1) (by rw [hw]; norm_num)
    rw [hy, MovingSofa.curveWinding_comp_of_reversed_endpoints
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 1) ⟨θ, hθ⟩ hφc hφ0 hφ1, hw]
    norm_num
  have hyarea : MovingSofa.curveAreaFunctional y = area γ :=
    MovingSofa.curveArea_eq_jordanInterior_area 0 1 (by norm_num) (trace γ) y hyori
  linarith

/-- Once the genuine winding orientation is known, the unsigned signed area is
the actual enclosed Lebesgue area, for either orientation. -/
theorem RectifiableJordan.abs_signedArea_eq_area_of_orientation (h : RectifiableJordan γ)
    (b : Bool)
    (hori : MovingSofa.IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1)
      (trace γ) b h.bvPath.val) : |MovingSofa.curveAreaFunctional h.bvPath| = area γ := by
  have hA : 0 ≤ area γ := ENNReal.toReal_nonneg
  cases b
  · rw [h.signedArea_eq_neg_area_of_clockwise hori, abs_neg, abs_of_nonneg hA]
  · rw [h.signedArea_eq_area_of_counterclockwise hori, abs_of_nonneg hA]

/-- The geometric equality-to-circle implication with the winding orientation
explicit. The unrestricted theorem in `Main.lean` derives this input geometrically. -/
theorem RectifiableJordan.circle_of_area_equality_of_orientation (h : RectifiableJordan γ)
    (b : Bool)
    (hori : MovingSofa.IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1)
      (trace γ) b h.bvPath.val)
    (heq : 4 * Real.pi * area γ = length γ ^ 2) :
    ∃ (c : Plane) (r : ℝ), 0 < r ∧ trace γ = Metric.sphere c r := by
  cases b
  · apply h.circle_of_signedArea_equality (-1) (by norm_num)
    rw [h.signedArea_arclengthParam, h.signedArea_eq_neg_area_of_clockwise hori]
    nlinarith [heq]
  · apply h.circle_of_signedArea_equality 1 (by norm_num)
    rw [h.signedArea_arclengthParam, h.signedArea_eq_area_of_counterclockwise hori]
    simpa using heq.symm

end Isoperimetric
