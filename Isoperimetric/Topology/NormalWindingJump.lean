/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Isoperimetric.Topology.ArgumentJump
import Isoperimetric.Topology.RegularPoint

/-!
# Unit winding jump across a regular point

Use a short normal segment at a regular arclength point to construct a relative complex
argument with exactly one downward branch-cut crossing. Its endpoint increment gives a
winding difference of one between the two sides.
-/

noncomputable section

open Set Complex Filter
open scoped Topology

namespace Isoperimetric

private theorem normal_relative_product (z V : ℂ) (α : ℝ) (hV : V ≠ 0) :
    starRingEnd ℂ (z + (α : ℂ) * I * V) * (z - (α : ℂ) * I * V) =
      (‖V‖ ^ 2 : ℝ) * ((‖z / V‖ ^ 2 - α ^ 2 : ℝ) -
        (2 * α * (z / V).re : ℝ) * I) := by
  have hz : z = V * (z / V) := by field_simp
  have he : z + (α : ℂ) * I * V = V * (z / V + (α : ℂ) * I) := by
    field_simp
  have he' : z - (α : ℂ) * I * V = V * (z / V - (α : ℂ) * I) := by
    field_simp
  rw [he, he', map_mul]
  have hp : starRingEnd ℂ (z / V + (α : ℂ) * I) * (z / V - (α : ℂ) * I) =
      (‖z / V‖ ^ 2 - α ^ 2 : ℝ) - (2 * α * (z / V).re : ℝ) * I := by
    generalize z / V = W
    apply Complex.ext <;>
      simp only [Complex.sq_norm, Complex.normSq_apply,
        map_add, map_mul, Complex.conj_re, Complex.conj_im, Complex.add_re,
        Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.mul_re,
        Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_sub,
        Complex.ofReal_mul, Complex.I_re, Complex.I_im] <;> ring
  calc
    _ = (starRingEnd ℂ V * V) *
        (starRingEnd ℂ (z / V + (α : ℂ) * I) * (z / V - (α : ℂ) * I)) := by ring
    _ = _ := by rw [Complex.conj_mul', hp, ← Complex.ofReal_pow]

/-- The winding differs by one across a unique normal crossing of a continuous loop.
The local hypotheses describe the sign of projection along its tangent. -/
theorem curveWinding_normal_jump {a b : ℝ} (hab : a < b)
    {x : Icc a b → Plane} (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab.le⟩ = x ⟨b, hab.le, le_rfl⟩)
    (c : Icc a b) (hc : (c : ℝ) ∈ Ioo a b) (v : Plane) (hv : v ≠ 0)
    {α : ℝ} (hα : 0 < α)
    (hcross : ∀ t : Icc a b, ∀ u : ℝ, |u| ≤ α →
      x t = x c + u • quarterTurn v → t = c ∧ u = 0)
    (hside : ∀ᶠ t in 𝓝 c,
      (t < c → (planeComplex (x t - x c) / planeComplex v).re < 0) ∧
      (c < t → 0 < (planeComplex (x t - x c) / planeComplex v).re)) :
    MovingSofa.curveWinding hab.le x (x c + α • quarterTurn v) -
      MovingSofa.curveWinding hab.le x (x c - α • quarterTurn v) = 1 := by
  let V := planeComplex v
  let w := fun t ↦ planeComplex (x t - x c) / V
  let p := x c + α • quarterTurn v
  let q := x c - α • quarterTurn v
  let R := fun t ↦ starRingEnd ℂ (planeComplex (x t - q)) * planeComplex (x t - p)
  have hV : V ≠ 0 := fun heq ↦ hv (planeComplex.map_eq_zero_iff.mp heq)
  have hVnorm : 0 < ‖V‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hV)
  have hp : p ∉ range x := by
    rintro ⟨t, ht⟩
    have := (hcross t α (by rw [abs_of_pos hα]) ht).2
    exact hα.ne' this
  have hq : q ∉ range x := by
    rintro ⟨t, ht⟩
    have heq : x t = x c + (-α) • quarterTurn v := by simpa [q, sub_eq_add_neg] using ht
    have := (hcross t (-α) (by rw [abs_neg, abs_of_pos hα]) heq).2
    linarith
  have hformula (t : Icc a b) : R t =
      (‖V‖ ^ 2 : ℝ) * ((‖w t‖ ^ 2 - α ^ 2 : ℝ) - (2 * α * (w t).re : ℝ) * I) := by
    have hplus : planeComplex (x t - q) = planeComplex (x t - x c) + (α : ℂ) * I * V := by
      simp only [q, map_sub, map_smul, planeComplex_quarterTurn, Complex.real_smul]
      ring
    have hminus : planeComplex (x t - p) = planeComplex (x t - x c) - (α : ℂ) * I * V := by
      simp only [p, map_sub, map_add, map_smul, planeComplex_quarterTurn, Complex.real_smul]
      ring
    dsimp only [R]
    rw [hplus, hminus]
    exact normal_relative_product _ V α hV
  have hRe (t : Icc a b) : (R t).re = ‖V‖ ^ 2 * (‖w t‖ ^ 2 - α ^ 2) := by
    rw [hformula]
    simp only [Complex.mul_re, Complex.sub_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
        sub_zero]
  have hIm (t : Icc a b) : (R t).im = ‖V‖ ^ 2 * (-2 * α * (w t).re) := by
    rw [hformula]
    simp only [Complex.sub_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hwc : w c = 0 := by simp [w]
  apply curveWinding_sub_eq_one_of_single_relative_crossing hab hx hclosed hp hq R
    (fun _ ↦ rfl) c hc
  · rw [hRe, hwc, norm_zero]
    nlinarith [sq_pos_of_pos hα]
  · rw [hIm, hwc]
    simp
  · intro t htc
    rw [mem_slitPlane_iff]
    by_cases hi : (R t).im = 0
    · left
      have hwRe : (w t).re = 0 := by
        rw [hIm] at hi
        have hf : -2 * α * (w t).re = 0 := (mul_eq_zero.mp hi).resolve_left hVnorm.ne'
        exact (mul_eq_zero.mp hf).resolve_left (mul_ne_zero (by norm_num) hα.ne')
      by_contra hneg
      have hnorm : ‖w t‖ ^ 2 ≤ α ^ 2 := by
        have := le_of_not_gt hneg
        rw [hRe] at this
        nlinarith
      have hu : |(w t).im| ≤ α := by
        rw [Complex.sq_norm, Complex.normSq_apply, hwRe] at hnorm
        apply (sq_le_sq₀ (abs_nonneg _) hα.le).mp
        rw [sq_abs]
        nlinarith [hnorm]
      have hw : w t = ((w t).im : ℂ) * I := by
        apply Complex.ext <;> simp [hwRe]
      have hxEq : x t = x c + (w t).im • quarterTurn v := by
        apply planeComplex.injective
        rw [map_add, map_smul, planeComplex_quarterTurn, Complex.real_smul]
        have hz : planeComplex (x t - x c) = V * w t := by
          dsimp [w]
          field_simp
        rw [map_sub] at hz
        rw [hw] at hz
        dsimp [V] at hz ⊢
        linear_combination hz
      exact htc (hcross t (w t).im hu hxEq).1
    · exact Or.inr hi
  · filter_upwards [hside] with t ht
    rw [hIm]
    constructor
    · intro htc
      have hwneg : (w t).re < 0 := ht.1 htc
      exact mul_pos hVnorm (mul_pos_of_neg_of_neg
        (mul_neg_of_neg_of_pos (by norm_num) hα) hwneg)
    · intro hct
      have hwpos : 0 < (w t).re := ht.2 hct
      exact mul_neg_of_pos_of_neg hVnorm (mul_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (by norm_num) hα) hwpos)

/-- Every permitted loop has two points off its arclength trace with winding
values differing by exactly one. -/
theorem RectifiableJordan.exists_winding_jump {γ : ℝ → Plane} (h : RectifiableJordan γ) :
    ∃ p q : Plane,
      p ∉ range (fun t : Icc (0 : ℝ) 1 ↦ arclengthParam γ t) ∧
      q ∉ range (fun t : Icc (0 : ℝ) 1 ↦ arclengthParam γ t) ∧
      MovingSofa.curveWinding (by norm_num : (0 : ℝ) ≤ 1)
        (fun t ↦ arclengthParam γ t) p -
      MovingSofa.curveWinding (by norm_num : (0 : ℝ) ≤ 1)
        (fun t ↦ arclengthParam γ t) q = 1 := by
  obtain ⟨t, ht, v, hv, _, ⟨δ, hδ, hsec⟩, β, hβ, hcross⟩ := h.exists_normal_crosscut
  let x : Icc (0 : ℝ) 1 → Plane := fun s ↦ arclengthParam γ s
  let c : Icc (0 : ℝ) 1 := ⟨t, ht.1.le, ht.2.le⟩
  let α := β / 2
  have hα : 0 < α := half_pos hβ
  have hxcross : ∀ s : Icc (0 : ℝ) 1, ∀ u : ℝ, |u| ≤ α →
      x s = x c + u • quarterTurn v → s = c ∧ u = 0 := by
    intro s u hu heq
    have huβ : |u| < β := lt_of_le_of_lt hu (by dsimp [α]; linarith)
    obtain ⟨hst, hu0⟩ := hcross s s.property u huβ heq
    exact ⟨Subtype.ext hst, hu0⟩
  let p := x c + α • quarterTurn v
  let q := x c - α • quarterTurn v
  have hp : p ∉ range x := by
    rintro ⟨s, hs⟩
    have hu0 := (hxcross s α (by rw [abs_of_pos hα]) hs).2
    exact hα.ne' hu0
  have hq : q ∉ range x := by
    rintro ⟨s, hs⟩
    have heq : x s = x c + (-α) • quarterTurn v := by simpa [q, sub_eq_add_neg] using hs
    have hu0 := (hxcross s (-α) (by rw [abs_neg, abs_of_pos hα]) heq).2
    linarith
  have hnear : ∀ᶠ s : Icc (0 : ℝ) 1 in 𝓝 c, |(s : ℝ) - t| < δ := by
    have hcT : Tendsto (fun s : Icc (0 : ℝ) 1 ↦ (s : ℝ)) (𝓝 c) (𝓝 t) :=
      continuous_subtype_val.continuousAt.tendsto
    have he := hcT.eventually (Metric.ball_mem_nhds t hδ)
    simpa only [Metric.mem_ball, Real.dist_eq] using he
  have hside : ∀ᶠ s in 𝓝 c,
      (s < c → (planeComplex (x s - x c) / planeComplex v).re < 0) ∧
      (c < s → 0 < (planeComplex (x s - x c) / planeComplex v).re) := by
    filter_upwards [hnear] with s hs
    constructor
    · intro hst
      have hslt : (s : ℝ) < t := hst
      have hpsec := hsec s hs hslt.ne
      rcases div_pos_iff.mp hpsec with ⟨_, hden⟩ | ⟨hn, _⟩
      · linarith
      · exact hn
    · intro hts
      have hsgt : t < (s : ℝ) := hts
      have hpsec := hsec s hs hsgt.ne'
      exact (div_pos_iff_of_pos_right (sub_pos.mpr hsgt)).mp hpsec
  refine ⟨p, q, hp, hq, ?_⟩
  have hx : Continuous x := continuousOn_iff_continuous_domRestrict.mp
    h.arclengthParam_isRectifiableJordan.continuousOn
  exact curveWinding_normal_jump (by norm_num : (0 : ℝ) < 1) hx
    h.arclengthParam_isRectifiableJordan.closed c ht v hv hα hxcross hside

end Isoperimetric
