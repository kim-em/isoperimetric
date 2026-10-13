import Isoperimetric.Analysis.Rotation
import MovingSofa.Curve.Jordan.WindingLifts

noncomputable section

open Set Complex

namespace Isoperimetric

private theorem planeComplex_re (v : Plane) : (planeComplex v).re = v 0 := by
  simp [planeComplex_apply]

private theorem planeComplex_im (v : Plane) : (planeComplex v).im = v 1 := by
  simp [planeComplex_apply]

/-- Positive relative radial dot products preserve winding when a closed loop changes. -/
theorem curveWinding_eq_of_positive_relative_product {a b : ℝ} (hab : a < b)
    {x y : Icc a b → Plane} (hx : Continuous x) (hy : Continuous y)
    (hxc : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (hyc : y ⟨a, le_rfl, hab.le⟩ = y ⟨b, hab.le, le_rfl⟩)
    {p : Plane} (hp : p ∉ range x)
    (hpos : ∀ t, 0 < (starRingEnd ℂ (planeComplex (x t - p)) *
      planeComplex (y t - p)).re) :
    MovingSofa.curveWinding hab.le y p = MovingSofa.curveWinding hab.le x p := by
  obtain ⟨θ, hθ⟩ := MovingSofa.exists_curveAngleLift_of_avoids hab hx hp
  let z := fun t ↦ planeComplex (x t - p)
  let w := fun t ↦ planeComplex (y t - p)
  let δ := fun t ↦ arg (starRingEnd ℂ (z t) * w t)
  have hz : Continuous z := planeComplex.continuous.comp (hx.sub continuous_const)
  have hw : Continuous w := planeComplex.continuous.comp (hy.sub continuous_const)
  have hδ : Continuous δ := MovingSofa.continuous_arg_conj_mul_of_re_pos hz hw hpos
  have hlift : MovingSofa.IsCurveAngleLift y p (fun t ↦ θ t + δ t) := by
    refine ⟨hθ.1.add hδ, fun t ↦ ?_⟩
    have hprod : starRingEnd ℂ (z t) * w t ≠ 0 := by
      intro heq
      have := hpos t
      change 0 < (starRingEnd ℂ (z t) * w t).re at this
      rw [heq] at this
      exact lt_irrefl _ this
    have hzne : z t ≠ 0 := fun heq ↦ hprod (by simp [heq])
    have hwne : w t ≠ 0 := fun heq ↦ hprod (by simp [heq])
    have hc : Real.cos (θ t) = (z t).re / ‖z t‖ := by
      simpa only [z, planeComplex_re, planeComplex_im, planeComplex.norm_map] using (hθ.2 t).1
    have hs : Real.sin (θ t) = (z t).im / ‖z t‖ := by
      simpa only [z, planeComplex_re, planeComplex_im, planeComplex.norm_map] using (hθ.2 t).2
    have hrot := MovingSofa.normalized_complex_rotation_by_relative_arg hzne hwne hc hs
    simpa only [w, δ, planeComplex_re, planeComplex_im, planeComplex.norm_map] using hrot
  have hδc : δ ⟨a, le_rfl, hab.le⟩ = δ ⟨b, hab.le, le_rfl⟩ := by
    simp only [δ, z, w, hxc, hyc]
  rw [hlift.curveWinding_eq hab.le, hθ.curveWinding_eq hab.le, hδc]
  ring

/-- Winding of a continuous loop is unchanged by sufficiently small uniform perturbations.
The perturbed loop needs only continuity and closure. -/
theorem exists_uniform_radius_preserving_winding {a b : ℝ} (hab : a < b)
    {x : Icc a b → Plane} (hx : Continuous x)
    (hxc : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    {p : Plane} (hp : p ∉ range x) :
    ∃ ε > 0, ∀ y : Icc a b → Plane, Continuous y →
      y ⟨a, le_rfl, hab.le⟩ = y ⟨b, hab.le, le_rfl⟩ →
      (∀ t, dist (y t) (x t) < ε) →
      MovingSofa.curveWinding hab.le y p = MovingSofa.curveWinding hab.le x p := by
  let _ : Nonempty (Icc a b) := ⟨⟨a, le_rfl, hab.le⟩⟩
  let f := fun t : Icc a b ↦ ‖x t - p‖
  have hf : Continuous f := (hx.sub continuous_const).norm
  obtain ⟨t₀, -, hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuousOn
  have hn (t : Icc a b) : 0 < ‖x t - p‖ := norm_pos_iff.mpr (by
    intro heq
    exact hp ⟨t, sub_eq_zero.mp heq⟩)
  refine ⟨f t₀ / 2, half_pos (hn t₀), fun y hy hyc hclose ↦ ?_⟩
  apply curveWinding_eq_of_positive_relative_product hab hx hy hxc hyc hp
  intro t
  have hd : ‖y t - x t‖ < ‖x t - p‖ := by
    have hm := hmin (mem_univ t)
    have hc := hclose t
    rw [dist_eq_norm] at hc
    dsimp [f] at hc hm
    linarith [hn t₀]
  have hprod : (starRingEnd ℂ (planeComplex (x t - p)) *
      planeComplex (y t - p)).re = inner ℝ (x t - p) (y t - p) := by
    simp [planeComplex_apply, inner, Fin.sum_univ_two]
    ring
  rw [hprod]
  have heq : y t - p = (x t - p) + (y t - x t) := by abel
  rw [heq, inner_add_right, real_inner_self_eq_norm_sq]
  have hlo := neg_le_of_abs_le (abs_real_inner_le_norm (x t - p) (y t - x t))
  nlinarith [hn t, norm_nonneg (y t - x t)]

end Isoperimetric
