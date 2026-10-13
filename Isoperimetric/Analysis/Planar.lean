/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Isoperimetric.Analysis.Loop
import Isoperimetric.Analysis.Wirtinger
import Isoperimetric.Analysis.Rotation

/-!
# Planar Wirtinger inequality for absolutely continuous loops

Project an absolutely continuous loop to each coordinate, identify coordinate
velocities almost everywhere, and sum the scalar Wirtinger estimates.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology Real Interval

namespace Isoperimetric

variable {η : ℝ → Plane}

/-- Projection to a coordinate commutes with differentiation almost everywhere. -/
theorem ACLoop.deriv_coordinate_ae (h : ACLoop η) (i : Fin 2) :
    (fun t ↦ deriv (fun s ↦ η s i) t) =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      (fun t ↦ deriv η t i) := by
  filter_upwards [h.ae_differentiableAt] with t ht
  exact ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivAt t ht.hasDerivAt).deriv

/-- Sharp planar Wirtinger for every closed absolutely continuous loop with L² velocity. -/
theorem ACLoop.wirtinger (h : ACLoop η) :
    (∫ t in (0 : ℝ)..1, ‖η t - ⨍ s in (0 : ℝ)..1, η s‖ ^ 2) ≤
      (1 / (2 * Real.pi)) ^ 2 * loopEnergy η := by
  let c := ⨍ s in (0 : ℝ)..1, η s
  let k := (1 / (2 * Real.pi)) ^ 2
  have hηint : IntervalIntegrable η volume 0 1 :=
    h.absolutelyContinuous.continuousOn.intervalIntegrable
  have hac := h.absolutelyContinuous_coordinate
  have hlp (i : Fin 2) : MemLp (fun t ↦ deriv (fun s ↦ η s i) t) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    rw [restrict_Ioc_eq_restrict_Icc]
    have hp : MemLp (fun t ↦ deriv η t i) 2
        (volume.restrict (Icc (0 : ℝ) 1)) :=
      (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' h.memLp_deriv
    exact hp.ae_eq (h.deriv_coordinate_ae i).symm
  have hmean (i : Fin 2) : (⨍ t in (0 : ℝ)..1, η t i) = c i := by
    change (⨍ t in (0 : ℝ)..1, (EuclideanSpace.proj (𝕜 := ℝ) i) (η t)) =
      (EuclideanSpace.proj (𝕜 := ℝ) i) c
    dsimp [c]
    simp only [interval_average_eq, sub_zero, inv_one, one_smul]
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).intervalIntegral_comp_comm
      hηint
  have hdev (i : Fin 2) : IntervalIntegrable (fun t ↦ (η t i - c i) ^ 2) volume 0 1 :=
    (((hac i).continuousOn.sub continuousOn_const).pow 2).intervalIntegrable
  have hdint (i : Fin 2) : IntervalIntegrable (fun t ↦ deriv η t i ^ 2) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr
    exact ((EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' h.memLp_deriv).integrable_sq
  have hscalar (i : Fin 2) : (∫ t in (0 : ℝ)..1, (η t i - c i) ^ 2) ≤
      k * ∫ t in (0 : ℝ)..1, deriv η t i ^ 2 := by
    have hs := wirtinger_real (by norm_num : (0 : ℝ) < 1) (hac i)
      (congrArg (fun z : Plane ↦ z i) h.closed) (hlp i)
    simp only [hmean i, Real.norm_eq_abs, sq_abs, sub_zero] at hs
    have hdintEq : (∫ t in (0 : ℝ)..1, deriv (fun s ↦ η s i) t ^ 2) =
        ∫ t in (0 : ℝ)..1, deriv η t i ^ 2 := by
      apply intervalIntegral.integral_congr_ae
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      have heq := h.deriv_coordinate_ae i
      rw [← restrict_Ioc_eq_restrict_Icc] at heq
      exact (ae_restrict_iff' measurableSet_Ioc).mp
        (heq.mono (fun _ ht ↦ congrArg (fun x : ℝ ↦ x ^ 2) ht))
    rw [hdintEq] at hs
    exact hs
  calc
    _ = (∫ t in (0 : ℝ)..1, (η t 0 - c 0) ^ 2) +
        ∫ t in (0 : ℝ)..1, (η t 1 - c 1) ^ 2 := by
      simp_rw [plane_norm_sq, PiLp.sub_apply]
      exact intervalIntegral.integral_add (hdev 0) (hdev 1)
    _ ≤ k * (∫ t in (0 : ℝ)..1, deriv η t 0 ^ 2) +
        k * ∫ t in (0 : ℝ)..1, deriv η t 1 ^ 2 := add_le_add (hscalar 0) (hscalar 1)
    _ = k * (∫ t in (0 : ℝ)..1, ‖deriv η t‖ ^ 2) := by
      rw [← mul_add, ← intervalIntegral.integral_add (hdint 0) (hdint 1)]
      simp_rw [plane_norm_sq]

end Isoperimetric
