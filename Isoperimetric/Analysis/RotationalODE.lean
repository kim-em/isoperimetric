/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Isoperimetric.Analysis.CompletionSquare
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Solving the circular ODE under absolute continuity

Multiply the complex representation of the centered loop by an integrating factor.
Its derivative vanishes almost everywhere, so absolute continuity makes it constant. No
pointwise differentiability assumption is needed.
-/

noncomputable section

open Set MeasureTheory Filter Complex
open scoped Topology Real Interval

namespace Isoperimetric

variable {η : ℝ → Plane}

/-- Solve the rotational ODE using absolute continuity and an integrating factor. -/
theorem solve_rotational_ode (hac : AbsolutelyContinuousOnInterval η 0 1)
    (c : Plane) (ω : ℝ)
    (hode : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      deriv η t = ω • quarterTurn (η t - c)) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      planeComplex (η t - c) =
        Complex.exp (((ω * t : ℝ) : ℂ) * I) * planeComplex (η 0 - c) := by
  let z : ℝ → ℂ := fun t ↦ planeComplex (η t - c)
  let e : ℝ → ℂ := fun t ↦ Complex.exp (-(((ω * t : ℝ) : ℂ) * I))
  let q : ℝ → ℂ := fun t ↦ e t * z t
  have hzAC : AbsolutelyContinuousOnInterval z 0 1 :=
    planeComplex.toContinuousLinearMap.lipschitzWith.comp_absolutelyContinuousOnInterval
      (hac.sub
        (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval)
  have heC1 : ContDiff ℝ 1 e := by
    have hi : ContDiff ℝ 1 (fun t : ℝ ↦ ω * t) := contDiff_const.mul contDiff_id
    have hh : ContDiff ℝ 1 (fun t : ℝ ↦ ((ω * t : ℝ) : ℂ) * I) :=
      ContDiff.mul (ofRealCLM.contDiff.comp hi) contDiff_const
    exact hh.neg.cexp
  have heAC : AbsolutelyContinuousOnInterval e 0 1 := heC1.contDiffOn.absolutelyContinuousOnInterval
  have hqAC : AbsolutelyContinuousOnInterval q 0 1 := by
    -- Complex multiplication is its scalar action; normalize those module instances.
    with_unfolding_all exact heAC.smul hzAC
  have heD (t : ℝ) : HasDerivAt e (-((ω : ℂ) * I) * e t) t := by
    have hi : HasDerivAt (fun s : ℝ ↦ -(((ω * s : ℝ) : ℂ) * I)) (-((ω : ℂ) * I)) t := by
      convert ((ofRealCLM.hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).const_mul ω)).mul_const I).neg using 1
      · funext s
        simp [Function.comp_apply, mul_comm]
      · simp
    simpa only [e, mul_comm] using hi.cexp
  have hqD : ∀ᵐ t ∂volume, t ∈ uIcc (0 : ℝ) 1 → HasDerivAt q 0 t := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    apply (ae_restrict_iff' measurableSet_Icc).mp
    have hd : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), DifferentiableAt ℝ η t := by
      rw [ae_restrict_iff' measurableSet_Icc]
      simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        hac.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
    filter_upwards [hd, hode] with t hdt hot
    have hηD := hdt.hasDerivAt
    have hzD : HasDerivAt z ((ω : ℂ) * I * z t) t := by
      have hD : HasDerivAt z (planeComplex (deriv η t)) t :=
        planeComplex.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t (hηD.sub_const c)
      rw [hot, planeComplex.map_smul, planeComplex_quarterTurn] at hD
      simpa [z, smul_eq_mul, mul_assoc] using hD
    have hD := (heD t).mul hzD
    have hzero : -((ω : ℂ) * I) * e t * z t + e t * ((ω : ℂ) * I * z t) = 0 := by ring
    rw [hzero] at hD
    exact hD
  obtain ⟨C, hC⟩ := hqAC.const_of_ae_hasDerivAt_zero hqD
  have hC0 : C = z 0 := by
    have h0 := hC 0 (by simp)
    simpa [q, e] using h0.symm
  intro t ht
  have hqt := hC t (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht)
  rw [hC0] at hqt
  have hprod := congrArg (fun w : ℂ ↦ Complex.exp (((ω * t : ℝ) : ℂ) * I) * w) hqt
  have hexp : Complex.exp (((ω * t : ℝ) : ℂ) * I) * e t = 1 := by
    dsimp [e]
    rw [← Complex.exp_add]
    simp
  change z t = _
  simpa only [q, ← mul_assoc, hexp, one_mul] using hprod

end Isoperimetric
