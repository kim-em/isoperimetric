import Isoperimetric.Topology.NormalWindingJump
import Isoperimetric.GeometricArea

noncomputable section

open Set

namespace Isoperimetric

/-- Winding is constant on every preconnected subset of the complement of a
continuous closed loop. This uses MovingSofa's local constancy theorem. -/
theorem curveWinding_eq_on_preconnected_complement {a b : ℝ} (hab : a ≤ b)
    {x : Icc a b → Plane} (hx : Continuous x)
    (hclosed : x ⟨a, le_rfl, hab⟩ = x ⟨b, hab, le_rfl⟩)
    {S : Set Plane} (hS : IsPreconnected S) (havoid : S ⊆ (range x)ᶜ)
    {p q : Plane} (hp : p ∈ S) (hq : q ∈ S) :
    MovingSofa.curveWinding hab x p = MovingSofa.curveWinding hab x q := by
  let _ : PreconnectedSpace S := Subtype.preconnectedSpace hS
  have hlc : IsLocallyConstant (fun z : S ↦ MovingSofa.curveWinding hab x z.val) := by
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro z
    obtain ⟨W, hW, hzW, heq⟩ := MovingSofa.curveWinding_locally_constant_off_range
      hab hx hclosed (havoid z.property)
    exact ⟨Subtype.val ⁻¹' W, hW.preimage continuous_subtype_val, hzW,
      fun z' hz' ↦ heq z'.val hz'⟩
  exact hlc.apply_eq_of_preconnectedSpace ⟨p, hp⟩ ⟨q, hq⟩

/-- The four geometric hypotheses imply a genuine winding orientation for the
arclength loop. No orientation is supplied as an additional assumption. -/
theorem RectifiableJordan.exists_orientation_arclength {γ : ℝ → Plane} (h : RectifiableJordan γ) :
    ∃ b : Bool, MovingSofa.IsOrientedJordanParametrization (by norm_num : (0 : ℝ) ≤ 1)
      (trace (arclengthParam γ)) b h.arclengthParam_isRectifiableJordan.bvPath.val := by
  let ha := h.arclengthParam_isRectifiableJordan
  let x := ha.bvPath.val
  have hx : Continuous x := ha.bvPath.property.1
  have hxclosed : x ⟨0, by norm_num⟩ = x ⟨1, by norm_num⟩ := ha.closed
  have hrange : range x = trace (arclengthParam γ) := ha.range_bvPath
  obtain ⟨U, V, hUopen, hVopen, hUconn, hVconn, hUb, hVb, hdisj, hcover,
    hfrontU, hfrontV, hcompU, hcompV⟩ := MovingSofa.jordan_separation ha.isJordanCurve
  have hUavoid : U ⊆ (range x)ᶜ := by
    rw [hrange]
    exact subset_union_left.trans hcover.subset
  have hVavoid : V ⊆ (range x)ᶜ := by
    rw [hrange]
    exact subset_union_right.trans hcover.subset
  have hUconst {p q : Plane} (hp : p ∈ U) (hq : q ∈ U) :
      MovingSofa.curveWinding (by norm_num : (0 : ℝ) ≤ 1) x p =
        MovingSofa.curveWinding (by norm_num : (0 : ℝ) ≤ 1) x q :=
    curveWinding_eq_on_preconnected_complement (by norm_num) hx hxclosed
      hUconn.isPreconnected hUavoid hp hq
  have hVzero {p : Plane} (hp : p ∈ V) :
      MovingSofa.curveWinding (by norm_num : (0 : ℝ) ≤ 1) x p = 0 := by
    apply MovingSofa.curveWinding_eq_zero_of_unbounded_component (by norm_num) hx hxclosed
      (hVavoid hp)
    rw [hrange, hcompV p hp]
    exact hVb
  have hIntU : MovingSofa.jordanInterior (trace (arclengthParam γ)) ⊆ U := by
    intro z hz
    have hzout := hz.1
    have hzUV : z ∈ U ∪ V := by rw [hcover]; exact hzout
    rcases hzUV with hzU | hzV
    · exact hzU
    · exact False.elim (hVb (by simpa only [hcompV z hzV] using hz.2))
  obtain ⟨p, q, hp, hq, hjump⟩ := h.exists_winding_jump
  change MovingSofa.curveWinding (by norm_num : (0 : ℝ) ≤ 1) x p -
    MovingSofa.curveWinding (by norm_num : (0 : ℝ) ≤ 1) x q = 1 at hjump
  have hpUV : p ∈ U ∪ V := by rw [hcover, ← hrange]; exact hp
  have hqUV : q ∈ U ∪ V := by rw [hcover, ← hrange]; exact hq
  have hwind : ∃ b : Bool, ∀ z ∈ MovingSofa.jordanInterior (trace (arclengthParam γ)),
      MovingSofa.curveWinding (by norm_num : (0 : ℝ) ≤ 1) x z = if b then 1 else -1 := by
    rcases hpUV with hpU | hpV <;> rcases hqUV with hqU | hqV
    · have heq := hUconst hpU hqU
      rw [heq, sub_self] at hjump
      norm_num at hjump
    · refine ⟨true, fun z hz ↦ ?_⟩
      rw [hVzero hqV, sub_zero] at hjump
      exact (hUconst (hIntU hz) hpU).trans hjump
    · refine ⟨false, fun z hz ↦ ?_⟩
      rw [hVzero hpV, zero_sub] at hjump
      have hqm : MovingSofa.curveWinding (by norm_num : (0 : ℝ) ≤ 1) x q = -1 := by linarith
      exact (hUconst (hIntU hz) hqU).trans hqm
    · rw [hVzero hpV, hVzero hqV] at hjump
      norm_num at hjump
  obtain ⟨b, hb⟩ := hwind
  refine ⟨b, by norm_num, ha.isJordanCurve, hx, hrange, hxclosed, ?_, hb⟩
  intro s hs t ht heq
  apply Subtype.ext
  exact ha.injectiveOn ⟨s.property.1, hs⟩ ⟨t.property.1, ht⟩ heq

end Isoperimetric
