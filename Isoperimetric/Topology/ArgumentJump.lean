/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Isoperimetric.Analysis.Rotation
import MovingSofa.Curve.Jordan.WindingLifts
import Mathlib.Topology.Piecewise

/-!
# Continuous argument across one branch-cut crossing

Correct the principal argument by a full turn at a single downward crossing. The resulting
continuous lift expresses a winding difference through its endpoint increment. The argument
uses only continuity, so no smooth approximation is required.
-/

noncomputable section

open Set Complex Filter
open scoped Topology

namespace Isoperimetric

/-- Correct the principal argument by one full turn at a single downward crossing
of its branch cut. The result is a continuous real argument on the interval. -/
theorem continuous_corrected_arg_of_single_crossing {a b : ℝ}
    {R : Icc a b → ℂ} (hR : Continuous R) (c : Icc a b)
    (hcRe : (R c).re < 0) (hcIm : (R c).im = 0)
    (haway : ∀ t, t ≠ c → R t ∈ slitPlane)
    (hside : ∀ᶠ t in 𝓝 c,
      (t < c → 0 < (R t).im) ∧ (c < t → (R t).im < 0)) :
    Continuous (fun t ↦ if t ≤ c then arg (R t) else arg (R t) + 2 * Real.pi) := by
  rw [continuous_iff_continuousAt]
  intro s
  rcases lt_trichotomy s c with hsc | hsc | hsc
  · have hg : ContinuousAt (fun t ↦ arg (R t)) s :=
      (continuousAt_arg (haway s hsc.ne)).comp hR.continuousAt
    apply hg.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hsc] with t ht
    simp only [ite_eq_left (show t ≤ c from ht.le)]
  · subst s
    have hslit : -R c ∈ slitPlane := Or.inl (by simp; linarith)
    have hg : ContinuousAt (fun t ↦ arg (-R t) + Real.pi) c :=
      ((continuousAt_arg hslit).comp_of_eq hR.neg.continuousAt rfl).add continuousAt_const
    apply hg.congr_of_eventuallyEq
    filter_upwards [hside] with t ht
    rcases lt_trichotomy t c with htc | htc | htc
    · have ha := arg_neg_eq_arg_sub_pi_of_im_pos (ht.1 htc)
      rw [ite_eq_left htc.le]
      linarith
    · subst t
      have ha := arg_neg_eq_arg_sub_pi_iff.mpr (Or.inr ⟨hcIm, hcRe⟩)
      rw [ite_eq_left le_rfl]
      linarith
    · have ha := arg_neg_eq_arg_add_pi_of_im_neg (ht.2 htc)
      rw [ite_eq_right (not_le.mpr htc)]
      linarith
  · have hg : ContinuousAt (fun t ↦ arg (R t) + 2 * Real.pi) s :=
      ((continuousAt_arg (haway s hsc.ne')).comp hR.continuousAt).add continuousAt_const
    apply hg.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hsc] with t ht
    simp only [ite_eq_right (not_le.mpr (show c < t from ht))]

/-- The continuous argument obtained at a single downward branch-cut crossing gains
exactly one full turn on a closed loop. -/
theorem exists_arg_lift_increment_two_pi_of_single_crossing {a b : ℝ}
    {R : Icc a b → ℂ} (hR : Continuous R) (c : Icc a b)
    (hc : (c : ℝ) ∈ Ioo a b)
    (hclosed : R ⟨a, le_rfl, c.property.1.trans c.property.2⟩ =
      R ⟨b, c.property.1.trans c.property.2, le_rfl⟩)
    (hne : ∀ t, R t ≠ 0) (hcRe : (R c).re < 0) (hcIm : (R c).im = 0)
    (haway : ∀ t, t ≠ c → R t ∈ slitPlane)
    (hside : ∀ᶠ t in 𝓝 c,
      (t < c → 0 < (R t).im) ∧ (c < t → (R t).im < 0)) :
    ∃ ψ : Icc a b → ℝ, Continuous ψ ∧
      (∀ t, Real.cos (ψ t) = (R t).re / ‖R t‖ ∧
        Real.sin (ψ t) = (R t).im / ‖R t‖) ∧
      ψ ⟨b, c.property.1.trans c.property.2, le_rfl⟩ -
        ψ ⟨a, le_rfl, c.property.1.trans c.property.2⟩ = 2 * Real.pi := by
  let ψ := fun t ↦ if t ≤ c then arg (R t) else arg (R t) + 2 * Real.pi
  refine ⟨ψ, continuous_corrected_arg_of_single_crossing hR c hcRe hcIm haway hside, ?_, ?_⟩
  · intro t
    dsimp only [ψ]
    split_ifs <;> simp only [Real.cos_add_two_pi, Real.sin_add_two_pi, cos_arg (hne t), sin_arg]
    <;> trivial
  · have hleft : (⟨a, le_rfl, c.property.1.trans c.property.2⟩ : Icc a b) ≤ c :=
      c.property.1
    have hright : ¬(⟨b, c.property.1.trans c.property.2, le_rfl⟩ : Icc a b) ≤ c :=
      not_le.mpr hc.2
    simp only [ψ, ite_eq_left hleft, ite_eq_right hright, hclosed]
    ring

/-- The increment of an argument of the relative radial product computes the
winding difference at two reference points. -/
theorem curveWinding_sub_eq_relative_arg_increment {a b : ℝ} (hab : a < b)
    {x : Icc a b → Plane} (hx : Continuous x) {p q : Plane}
    (hp : p ∉ range x) (hq : q ∉ range x)
    {ψ : Icc a b → ℝ} (hψ : Continuous ψ)
    (hψdir : ∀ t, let R := starRingEnd ℂ (planeComplex (x t - q)) * planeComplex (x t - p)
      Real.cos (ψ t) = R.re / ‖R‖ ∧ Real.sin (ψ t) = R.im / ‖R‖) :
    MovingSofa.curveWinding hab.le x p - MovingSofa.curveWinding hab.le x q =
      (ψ ⟨b, hab.le, le_rfl⟩ - ψ ⟨a, le_rfl, hab.le⟩) / (2 * Real.pi) := by
  obtain ⟨θ, hθ⟩ := MovingSofa.exists_curveAngleLift_of_avoids hab hx hq
  have hlift : MovingSofa.IsCurveAngleLift x p (fun t ↦ θ t + ψ t) := by
    refine ⟨hθ.1.add hψ, fun t ↦ ?_⟩
    let z := planeComplex (x t - q)
    let w := planeComplex (x t - p)
    have hz : z ≠ 0 := by
      intro heq
      have hxq : x t - q = 0 := planeComplex.map_eq_zero_iff.mp heq
      exact hq ⟨t, sub_eq_zero.mp hxq⟩
    have hw : w ≠ 0 := by
      intro heq
      have hxp : x t - p = 0 := planeComplex.map_eq_zero_iff.mp heq
      exact hp ⟨t, sub_eq_zero.mp hxp⟩
    have hR : starRingEnd ℂ z * w ≠ 0 := mul_ne_zero (by simpa using hz) hw
    have hc : Real.cos (θ t) = z.re / ‖z‖ := by
      simpa only [z, planeComplex_re, planeComplex.norm_map] using (hθ.2 t).1
    have hs : Real.sin (θ t) = z.im / ‖z‖ := by
      simpa only [z, planeComplex_im, planeComplex.norm_map] using (hθ.2 t).2
    have hrot := MovingSofa.normalized_complex_rotation_by_relative_arg hz hw hc hs
    have hcos : Real.cos (ψ t) = Real.cos (arg (starRingEnd ℂ z * w)) := by
      rw [cos_arg hR]
      exact (hψdir t).1
    have hsin : Real.sin (ψ t) = Real.sin (arg (starRingEnd ℂ z * w)) := by
      rw [sin_arg]
      exact (hψdir t).2
    have hcosadd : Real.cos (θ t + ψ t) = Real.cos (θ t + arg (starRingEnd ℂ z * w)) := by
      rw [Real.cos_add, Real.cos_add, hcos, hsin]
    have hsinadd : Real.sin (θ t + ψ t) = Real.sin (θ t + arg (starRingEnd ℂ z * w)) := by
      rw [Real.sin_add, Real.sin_add, hcos, hsin]
    rw [hcosadd, hsinadd]
    simpa only [w, planeComplex_re, planeComplex_im, planeComplex.norm_map] using hrot
  rw [hlift.curveWinding_eq hab.le, hθ.curveWinding_eq hab.le]
  ring

/-- A single downward branch-cut crossing of the relative radial product gives
an exact unit jump between the topological winding values of a continuous loop. -/
theorem curveWinding_sub_eq_one_of_single_relative_crossing {a b : ℝ} (hab : a < b)
    {x : Icc a b → Plane} (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    {p q : Plane} (hp : p ∉ range x) (hq : q ∉ range x)
    (R : Icc a b → ℂ)
    (hR : ∀ t, R t = starRingEnd ℂ (planeComplex (x t - q)) * planeComplex (x t - p))
    (c : Icc a b) (hc : (c : ℝ) ∈ Ioo a b)
    (hcRe : (R c).re < 0) (hcIm : (R c).im = 0)
    (haway : ∀ t, t ≠ c → R t ∈ slitPlane)
    (hside : ∀ᶠ t in 𝓝 c,
      (t < c → 0 < (R t).im) ∧ (c < t → (R t).im < 0)) :
    MovingSofa.curveWinding hab.le x p - MovingSofa.curveWinding hab.le x q = 1 := by
  have hcont : Continuous R := by
    have heq : R = fun t ↦ starRingEnd ℂ (planeComplex (x t - q)) * planeComplex (x t - p) :=
      funext hR
    rw [heq]
    exact (continuous_star.comp (planeComplex.continuous.comp (hx.sub continuous_const))).mul
      (planeComplex.continuous.comp (hx.sub continuous_const))
  have hRc : R ⟨a, le_rfl, hab.le⟩ = R ⟨b, hab.le, le_rfl⟩ := by
    simp only [hR, hclosed]
  have hne : ∀ t, R t ≠ 0 := by
    intro t
    rw [hR t]
    apply mul_ne_zero
    · apply (map_ne_zero (starRingEnd ℂ)).mpr
      intro heq
      have hzero : x t - q = 0 := planeComplex.map_eq_zero_iff.mp heq
      exact hq ⟨t, sub_eq_zero.mp hzero⟩
    · intro heq
      have hzero : x t - p = 0 := planeComplex.map_eq_zero_iff.mp heq
      exact hp ⟨t, sub_eq_zero.mp hzero⟩
  obtain ⟨ψ, hψ, hdir, hinc⟩ := exists_arg_lift_increment_two_pi_of_single_crossing
    hcont c hc hRc hne hcRe hcIm haway hside
  have hdirection : ∀ t,
      let z := starRingEnd ℂ (planeComplex (x t - q)) * planeComplex (x t - p)
      Real.cos (ψ t) = z.re / ‖z‖ ∧ Real.sin (ψ t) = z.im / ‖z‖ := by
    intro t
    simpa only [hR t] using hdir t
  rw [curveWinding_sub_eq_relative_arg_increment hab hx hp hq hψ hdirection, hinc]
  exact div_self (mul_ne_zero (by norm_num) Real.pi_ne_zero)

end Isoperimetric
