/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import MovingSofa.Analysis.Stieltjes.AbsoluteContinuity

/-!
# Stieltjes density for absolutely continuous coordinates

Identify the interval Stieltjes measure with the almost-everywhere derivative density.
This bridge supports singular original parametrizations by applying only after arclength
normalization.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace Isoperimetric

/-- Identify the Stieltjes density of an absolutely continuous coordinate using
its almost-everywhere derivative. No everywhere-differentiability hypothesis is needed. -/
theorem hasIntervalStieltjesDensity_of_absolutelyContinuous {a b : ℝ} (hab : a ≤ b)
    (F : MovingSofa.RightContinuousIntervalBV a b) (φ : ℝ → ℝ)
    (hF : ∀ t : Icc a b, F.toFun t = φ t)
    (hac : AbsolutelyContinuousOnInterval φ a b) :
    MovingSofa.HasIntervalStieltjesDensity F (deriv φ) := by
  have hext : EqOn (MovingSofa.stieltjesScalarExtension F) φ (Icc a b) := by
    intro t ht
    simp only [MovingSofa.stieltjesScalarExtension, dite_eq_left ht]
    exact hF ⟨t, ht⟩
  have hac' : AbsolutelyContinuousOnInterval (MovingSofa.stieltjesScalarExtension F) a b :=
    hac.congr (fun t ht ↦ (hext (by simpa only [uIcc_of_le hab] using ht)).symm)
  obtain ⟨ρ, hρ⟩ := (MovingSofa.intervalStieltjes_absoluteContinuity a b hab F).1.mp hac'
  have hd := (MovingSofa.intervalStieltjes_absoluteContinuity a b hab F).2 ρ hρ
  have heq : ρ =ᵐ[volume.restrict (Icc a b)] deriv φ := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [hd, ae_restrict_mem measurableSet_Ioo] with t ht hto
    have hevent : φ =ᶠ[𝓝 t] MovingSofa.stieltjesScalarExtension F := by
      filter_upwards [isOpen_Ioo.mem_nhds hto] with s hs
      exact (hext ⟨hs.1.le, hs.2.le⟩).symm
    exact (ht.congr_of_eventuallyEq hevent).deriv.symm
  refine ⟨hρ.1.congr heq, ?_⟩
  intro E hE
  rw [hρ.2 E hE]
  exact integral_congr_ae (ae_restrict_of_ae heq)

end Isoperimetric
