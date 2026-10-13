import Isoperimetric.Jordan
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

noncomputable section

open Set MeasureTheory Metric

namespace Isoperimetric

private theorem ball_subset_sphere_compl (c : Plane) (r : ℝ) :
    ball c r ⊆ (sphere c r)ᶜ := by
  intro p hp hs
  exact (mem_ball.mp hp).ne (mem_sphere.mp hs)

/-- The component of a point inside a sphere is its open ball. -/
theorem connectedComponentIn_sphere_compl_of_mem_ball (c p : Plane) (r : ℝ)
    (hp : p ∈ ball c r) : connectedComponentIn (sphere c r)ᶜ p = ball c r := by
  apply Subset.antisymm
  · intro q hq
    have hpcomp : p ∈ connectedComponentIn (sphere c r)ᶜ p :=
      mem_connectedComponentIn (ball_subset_sphere_compl c r hp)
    by_contra hqb
    have hqd : r ≤ dist q c := le_of_not_gt (by simpa [mem_ball] using hqb)
    have hpd : dist p c < r := mem_ball.mp hp
    have hconn : IsPreconnected ((fun z : Plane ↦ dist z c) '' connectedComponentIn (sphere c r)ᶜ p) :=
      isPreconnected_connectedComponentIn.image _ (continuous_id.dist continuous_const).continuousOn
    have hrim : r ∈ (fun z : Plane ↦ dist z c) '' connectedComponentIn (sphere c r)ᶜ p :=
      hconn.ordConnected.out ⟨p, hpcomp, rfl⟩ ⟨q, hq, rfl⟩ ⟨hpd.le, hqd⟩
    obtain ⟨z, hz, hzr⟩ := hrim
    exact (connectedComponentIn_subset _ _ hz) (mem_sphere.mpr hzr)
  · exact isPreconnected_ball.subset_connectedComponentIn hp (ball_subset_sphere_compl c r)

/-- Outside a sphere, an outward ray lies in the same complementary component. -/
theorem sphere_compl_component_unbounded_of_lt (c p : Plane) (r : ℝ)
    (hr : 0 < r) (hp : r < dist p c) :
    ¬Bornology.IsBounded (connectedComponentIn (sphere c r)ᶜ p) := by
  let ray : ℝ → Plane := fun t ↦ c + t • (p - c)
  have hd : 0 < ‖p - c‖ := hr.trans (by simpa [dist_eq_norm] using hp)
  have hpre : IsPreconnected (ray '' Ici 1) :=
    isPreconnected_Ici.image ray (continuous_const.add (continuous_id.smul continuous_const)).continuousOn
  have hpray : p ∈ ray '' Ici 1 := by
    refine ⟨1, by simp, ?_⟩
    simp [ray]
  have hsub : ray '' Ici 1 ⊆ (sphere c r)ᶜ := by
    rintro q ⟨t, ht, rfl⟩ hq
    have ht0 : 0 ≤ t := zero_le_one.trans ht
    have hn : dist (ray t) c = t * ‖p - c‖ := by
      simp [ray, dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    have hgt : r < t * ‖p - c‖ := by
      have hpd : r < ‖p - c‖ := by simpa [dist_eq_norm] using hp
      exact hpd.trans_le (le_mul_of_one_le_left hd.le ht)
    exact hgt.ne' (hn.symm.trans (mem_sphere.mp hq))
  have hcomp := hpre.subset_connectedComponentIn hpray hsub
  intro hb
  obtain ⟨R, hR⟩ := hb.exists_norm_le
  let t := (max R 0 + ‖c‖ + ‖p - c‖ + 1) / ‖p - c‖
  have ht : 1 ≤ t := by
    apply (le_div_iff₀ hd).mpr
    have hm : 0 ≤ max R 0 := le_max_right _ _
    linarith [norm_nonneg c]
  have hn : ‖ray t - c‖ = max R 0 + ‖c‖ + ‖p - c‖ + 1 := by
    simp only [ray, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (zero_le_one.trans ht)]
    exact div_mul_cancel₀ _ hd.ne'
  have hbound : ‖ray t‖ ≤ R := hR _ (hcomp ⟨t, ht, rfl⟩)
  have htriangle := norm_sub_le (ray t) c
  rw [hn] at htriangle
  linarith [le_max_left R 0]

/-- The genuine Jordan interior of a positive-radius circle is its open disk. -/
theorem jordanInterior_sphere (c : Plane) (r : ℝ) (hr : 0 < r) :
    MovingSofa.jordanInterior (sphere c r) = ball c r := by
  ext p
  change (p ∉ sphere c r ∧ Bornology.IsBounded (connectedComponentIn (sphere c r)ᶜ p)) ↔ p ∈ ball c r
  constructor
  · rintro ⟨hpn, hpb⟩
    by_contra hpout
    have hple : r ≤ dist p c := le_of_not_gt (by simpa [mem_ball] using hpout)
    have hpne : dist p c ≠ r := fun hpr ↦ hpn (mem_sphere.mpr hpr)
    exact sphere_compl_component_unbounded_of_lt c p r hr (lt_of_le_of_ne hple hpne.symm) hpb
  · intro hp
    refine ⟨ball_subset_sphere_compl c r hp, ?_⟩
    rw [connectedComponentIn_sphere_compl_of_mem_ball c p r hp]
    exact isBounded_ball

theorem enclosed_of_trace_sphere {γ : ℝ → Plane} (c : Plane) (r : ℝ) (hr : 0 < r)
    (htrace : trace γ = sphere c r) : enclosed γ = ball c r := by
  rw [enclosed, htrace, jordanInterior_sphere c r hr]

theorem area_of_trace_sphere {γ : ℝ → Plane} (c : Plane) (r : ℝ) (hr : 0 < r)
    (htrace : trace γ = sphere c r) : area γ = Real.pi * r ^ 2 := by
  rw [area, enclosed_of_trace_sphere c r hr htrace, EuclideanSpace.volume_ball_fin_two,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le,
    ENNReal.toReal_ofReal Real.pi_pos.le]
  ring

end Isoperimetric
