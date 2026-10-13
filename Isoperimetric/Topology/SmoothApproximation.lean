import Isoperimetric.Topology.RegularPoint
import Isoperimetric.Topology.WindingStability
import TauCeti.Analysis.Contour.Curve.Approximation

noncomputable section

open Set
open scoped unitInterval

namespace Isoperimetric

/-- A continuous planar loop has smooth complex approximants with the same endpoints.
The approximation is uniform on the full closed parameter interval. -/
theorem RectifiableJordan.exists_smooth_complex_approximation {γ : ℝ → Plane}
    (h : RectifiableJordan γ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ζ : ℝ → ℂ, ContDiff ℝ ⊤ ζ ∧
      ζ 0 = planeComplex (γ 0) ∧ ζ 1 = planeComplex (γ 1) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, dist (ζ t) (planeComplex (γ t)) < ε := by
  let f : C(I, ℂ) := ⟨fun t ↦ planeComplex (γ t),
    planeComplex.continuous.comp (continuousOn_iff_continuous_domRestrict.mp h.continuousOn)⟩
  obtain ⟨ζ, hζ, hζ0, hζ1, hclose⟩ :=
    TauCeti.Contour.exists_contDiff_eq_endpoints_dist_lt f hε
  exact ⟨ζ, hζ, hζ0, hζ1, fun t ht ↦ hclose ⟨t, ht⟩⟩

/-- Smooth approximation can preserve the topological winding around any point off the trace.
No differentiability of the original parametrization is required. -/
theorem RectifiableJordan.exists_smooth_approximation_preserving_winding {γ : ℝ → Plane}
    (h : RectifiableJordan γ) {p : Plane} (hp : p ∉ trace γ) :
    ∃ ζ : ℝ → ℂ, ContDiff ℝ ⊤ ζ ∧
      ζ 0 = planeComplex (γ 0) ∧ ζ 1 = planeComplex (γ 1) ∧
      MovingSofa.curveWinding (by norm_num : (0 : ℝ) ≤ 1)
        (fun t ↦ planeComplex.symm (ζ t)) p =
      MovingSofa.curveWinding (by norm_num : (0 : ℝ) ≤ 1) (fun t ↦ γ t) p := by
  let x : Icc (0 : ℝ) 1 → Plane := fun t ↦ γ t
  have hx : Continuous x := continuousOn_iff_continuous_domRestrict.mp h.continuousOn
  have hxc : x ⟨0, le_rfl, by norm_num⟩ = x ⟨1, by norm_num, le_rfl⟩ := h.closed
  have hp' : p ∉ range x := by
    rintro ⟨t, ht⟩
    exact hp ⟨t, t.property, ht⟩
  obtain ⟨ε, hε, hstable⟩ := exists_uniform_radius_preserving_winding
    (by norm_num : (0 : ℝ) < 1) hx hxc hp'
  obtain ⟨ζ, hζ, hζ0, hζ1, hclose⟩ := h.exists_smooth_complex_approximation hε
  let y : Icc (0 : ℝ) 1 → Plane := fun t ↦ planeComplex.symm (ζ t)
  have hy : Continuous y := planeComplex.symm.continuous.comp
    (hζ.continuous.comp continuous_subtype_val)
  have hyc : y ⟨0, le_rfl, by norm_num⟩ = y ⟨1, by norm_num, le_rfl⟩ := by
    simp only [y, hζ0, hζ1, planeComplex.symm_apply_apply, h.closed]
  have hdist : ∀ t, dist (y t) (x t) < ε := by
    intro t
    calc
      dist (y t) (x t) = dist (ζ t) (planeComplex (γ t)) := by
        rw [← planeComplex.isometry.dist_eq (y t) (x t)]
        simp only [y, x, planeComplex.apply_symm_apply]
      _ < ε := hclose t t.property
  exact ⟨ζ, hζ, hζ0, hζ1, hstable y hy hyc hdist⟩

end Isoperimetric
