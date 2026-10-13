/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Isoperimetric.Jordan
import MovingSofa.ForMathlib.MeasureTheory.Hausdorff.Arclength
import Submission

/-!
# Normalizing the geometric boundary inequality

Reconcile raw and Euclidean-normalized Hausdorff measures in dimension one and specialize
Humanfia's geometric isoperimetric inequality to two dimensions. This bridge keeps every
normalization factor explicit.
-/

noncomputable section

open Set MeasureTheory MeasureTheory.Measure

namespace Isoperimetric

-- The isometry's measurable-space instances need reducible unfolding in the
-- measure-preserving rewrite. Restrict that elaboration setting to this theorem.
set_option backward.isDefEq.respectTransparency false in
/-- In dimension one the raw and Euclidean-normalized Hausdorff measures coincide. -/
theorem euclideanHausdorffMeasure_one_eq_hausdorffMeasure
    {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X] :
    (euclideanHausdorffMeasure 1 : Measure X) = hausdorffMeasure 1 := by
  let e := (OrthonormalBasis.singleton (Fin 1) ℝ).repr
  have heq : (hausdorffMeasure 1 : Measure (EuclideanSpace ℝ (Fin 1))) = volume := by
    have hm := e.isometry.map_hausdorffMeasure (d := 1) (Or.inr e.surjective)
    rw [hausdorffMeasure_real, e.measurePreserving.map_eq,
      e.surjective.range_eq, Measure.restrict_univ] at hm
    exact hm.symm
  simp [euclideanHausdorffMeasure_def, heq]

/-- Humanfia's geometric theorem specialized to planar Lebesgue area and raw length. -/
theorem planar_boundary_inequality (B : Set Plane) (hBm : MeasurableSet B)
    (hBb : Bornology.IsBounded B) :
    4 * volume B * ENNReal.ofReal Real.pi ≤ (hausdorffMeasure 1 (frontier B)) ^ 2 := by
  have h := Submission.isoperimetric 2 (by norm_num) B hBm hBb
  norm_num [EuclideanSpace.volume_closedBall_fin_two,
    euclideanHausdorffMeasure_one_eq_hausdorffMeasure] at h ⊢
  exact h

end Isoperimetric
