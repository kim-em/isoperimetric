/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The Fourier coefficient algebra adapts Mathlib.Analysis.Fourier.AddCircle
(Heather Macbeth and David Loeffler) at c32e1ec0d1eb5237ba344eee50162f45d5b0fc76.
The Parseval argument adapts TauCeti.Analysis.Fourier.Wirtinger at
8014353f314435299acce5b6faa19d781530cfa2. The integration-by-parts bridge is
extended here to absolutely continuous real functions, and scalar Wirtinger
therefore needs no everywhere-differentiability assumption.
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalAverage

noncomputable section
open MeasureTheory Set Complex intervalIntegral
open scoped Real Interval

namespace Isoperimetric

theorem integral_mul_complex_deriv {a b : ℝ} {f : ℝ → ℝ} {g g' : ℝ → ℂ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g') :
    (∫ x in a..b, (f x : ℂ) * g' x) =
      (f b : ℂ) * g b - (f a : ℂ) * g a - ∫ x in a..b, ((deriv f x : ℝ) : ℂ) * g x := by
  have hgc : Continuous g := continuous_iff_continuousAt.mpr (fun x ↦ (hg x).continuousAt)
  have hC1 : ContDiff ℝ 1 g := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun x ↦ (hg x).differentiableAt, ?_⟩
    convert hg' using 1
    funext x
    exact (hg x).deriv
  have hgac := hC1.contDiffOn.absolutelyContinuousOnInterval (a := a) (b := b)
  have hreac : AbsolutelyContinuousOnInterval (fun x ↦ (g x).re) a b :=
    reCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hgac
  have himac : AbsolutelyContinuousOnInterval (fun x ↦ (g x).im) a b :=
    imCLM.lipschitzWith.comp_absolutelyContinuousOnInterval hgac
  have hdre (x : ℝ) : deriv (fun y ↦ (g y).re) x = (g' x).re :=
    (reCLM.hasFDerivAt.comp_hasDerivAt x (hg x)).deriv
  have hdim (x : ℝ) : deriv (fun y ↦ (g y).im) x = (g' x).im :=
    (imCLM.hasFDerivAt.comp_hasDerivAt x (hg x)).deriv
  have hL : IntervalIntegrable (fun x ↦ (f x : ℂ) * g' x) volume a b :=
    ((Complex.continuous_ofReal.comp_continuousOn hf.continuousOn).mul hg'.continuousOn).intervalIntegrable
  have hD : IntervalIntegrable (fun x ↦ ((deriv f x : ℝ) : ℂ)) volume a b :=
    intervalIntegrable_iff.mpr (ofRealCLM.integrable_comp hf.intervalIntegrable_deriv.def')
  have hR : IntervalIntegrable (fun x ↦ ((deriv f x : ℝ) : ℂ) * g x) volume a b :=
    hD.mul_continuousOn hgc.continuousOn
  apply Complex.ext
  · have he := hf.integral_mul_deriv_eq_deriv_mul hreac
    simp_rw [hdre] at he
    have hleft : (∫ x in a..b, (f x : ℂ) * g' x).re =
        ∫ x in a..b, f x * (g' x).re := by
      simpa using (reCLM.intervalIntegral_comp_comm hL).symm
    have hright : (∫ x in a..b, ((deriv f x : ℝ) : ℂ) * g x).re =
        ∫ x in a..b, deriv f x * (g x).re := by
      simpa using (reCLM.intervalIntegral_comp_comm hR).symm
    rw [hleft, Complex.sub_re, Complex.sub_re, hright]
    simpa using he
  · have he := hf.integral_mul_deriv_eq_deriv_mul himac
    simp_rw [hdim] at he
    have hleft : (∫ x in a..b, (f x : ℂ) * g' x).im =
        ∫ x in a..b, f x * (g' x).im := by
      simpa using (imCLM.intervalIntegral_comp_comm hL).symm
    have hright : (∫ x in a..b, ((deriv f x : ℝ) : ℂ) * g x).im =
        ∫ x in a..b, deriv f x * (g x).im := by
      simpa using (imCLM.intervalIntegral_comp_comm hR).symm
    rw [hleft, Complex.sub_im, Complex.sub_im, hright]
    simpa using he

/- This coefficient identity adapts Mathlib's Fourier coefficient integration-by-parts
proof to an absolutely continuous real function. -/
theorem fourierCoeffOn_of_absolutelyContinuous {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    {n : ℤ} (hn : n ≠ 0) (hf : AbsolutelyContinuousOnInterval f a b) :
    fourierCoeffOn hab (fun x ↦ (f x : ℂ)) n = 1 / (-2 * π * I * n) *
      (fourier (-n) (a : AddCircle (b - a)) * ((f b : ℂ) - (f a : ℂ)) -
        (b - a) * fourierCoeffOn hab (fun x ↦ ((deriv f x : ℝ) : ℂ)) n) := by
  rw [← ofReal_sub]
  have hT : Fact (0 < b - a) := ⟨by linarith⟩
  simp_rw [fourierCoeffOn_eq_integral, smul_eq_mul, real_smul, ofReal_div, ofReal_one]
  conv => pattern (occs := 1 2 3) fourier _ _ * _ <;> rw [mul_comm]
  rw [integral_mul_complex_deriv hf
    (fun x ↦ has_antideriv_at_fourier_neg hT hn x)
    ((map_continuous (fourier (-n))).comp (AddCircle.continuous_mk' _))]
  have halg : ∀ u v w : ℂ, u * ((b - a : ℝ) / v * w) = (b - a : ℝ) / v * (u * w) :=
    by intros; ring
  conv in intervalIntegral _ _ _ _ => congr; ext; rw [halg]
  rw [(by ring : ((b - a : ℝ) : ℂ) / (-2 * π * I * n) =
    ((b - a : ℝ) : ℂ) * (1 / (-2 * π * I * n)))]
  have hperiod : (b : AddCircle (b - a)) = (a : AddCircle (b - a)) := by
    simpa using AddCircle.coe_add_period (b - a) a
  rw [hperiod, intervalIntegral.integral_const_mul, ← sub_mul, mul_sub, mul_sub]
  congr 1
  · conv_lhs => rw [mul_comm, mul_div, mul_one]
    rw [div_eq_iff (ofReal_ne_zero.mpr hT.out.ne')]
    simp only [ofReal_sub]
    ring
  · simp only [ofReal_sub]
    ring

theorem wirtinger_real {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hfab : f a = f b)
    (hf' : MemLp (deriv f) 2 (volume.restrict (Ioc a b))) :
    (∫ x in a..b, ‖f x - ⨍ y in a..b, f y‖ ^ 2) ≤
      ((b - a) / (2 * π)) ^ 2 * ∫ x in a..b, ‖deriv f x‖ ^ 2 := by
  set m := ⨍ y in a..b, f y
  set g : ℝ → ℝ := fun x ↦ f x - m
  have hba : 0 < b - a := sub_pos.mpr hab
  have hgac : AbsolutelyContinuousOnInterval g a b := hf.sub
    (LipschitzWith.const m).lipschitzOnWith.absolutelyContinuousOnInterval
  have hgc : ContinuousOn (fun x ↦ (g x : ℂ)) (Icc a b) :=
    Complex.continuous_ofReal.comp_continuousOn (by
      simpa only [uIcc_of_le hab.le] using hgac.continuousOn)
  have hgL2 : MemLp (fun x ↦ (g x : ℂ)) 2 (volume.restrict (Ioc a b)) := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
    exact MemLp.of_bound ((hgc.aestronglyMeasurable measurableSet_Icc).mono_set Ioc_subset_Icc_self)
      C (ae_restrict_of_forall_mem measurableSet_Ioc
        (fun x hx ↦ hC x (Ioc_subset_Icc_self hx)))
  have hfCL2 := ofRealCLM.comp_memLp' hf'
  have hmean : (∫ x in a..b, g x) = 0 := by
    rw [intervalIntegral.integral_sub hf.continuousOn.intervalIntegrable intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    dsimp [m]
    rw [interval_average_eq]
    simp [smul_eq_mul, hba.ne']
  have hcoeff (n : ℤ) : ‖fourierCoeffOn hab (fun x ↦ (g x : ℂ)) n‖ ^ 2 ≤
      ((b - a) / (2 * π)) ^ 2 *
        ‖fourierCoeffOn hab (fun x ↦ ((deriv f x : ℝ) : ℂ)) n‖ ^ 2 := by
    rcases eq_or_ne n 0 with rfl | hn
    · have hzero : fourierCoeffOn hab (fun x ↦ (g x : ℂ)) 0 = 0 := by
        simp [fourierCoeffOn_eq_integral, intervalIntegral.integral_ofReal, hmean]
      simpa [hzero] using (by positivity : 0 ≤ ((b - a) / (2 * π)) ^ 2 *
        ‖fourierCoeffOn hab (fun x ↦ ((deriv f x : ℝ) : ℂ)) 0‖ ^ 2)
    · have hn' : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      have hnorm : ‖fourierCoeffOn hab (fun x ↦ (g x : ℂ)) n‖ =
          (b - a) / (2 * π) / |(n : ℝ)| *
            ‖fourierCoeffOn hab (fun x ↦ ((deriv f x : ℝ) : ℂ)) n‖ := by
        rw [fourierCoeffOn_of_absolutelyContinuous hab hn hgac]
        simp [g, hfab, ← ofReal_sub, abs_of_pos hba, abs_of_pos Real.pi_pos]
        field_simp
      rw [hnorm, mul_pow]
      gcongr ?_ ^ 2 * _
      exact div_le_self (by positivity) hn'
  have hsum := hasSum_le hcoeff (hasSum_sq_fourierCoeffOn hab hgL2)
    ((hasSum_sq_fourierCoeffOn hab hfCL2).mul_left (((b - a) / (2 * π)) ^ 2))
  rw [smul_eq_mul, smul_eq_mul, mul_left_comm] at hsum
  have hres := le_of_mul_le_mul_left hsum (inv_pos.mpr hba)
  simpa only [g, Function.comp_apply, ofRealCLM_apply, Complex.norm_real,
    Real.norm_eq_abs] using hres

end Isoperimetric
