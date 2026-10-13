/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Isoperimetric.Jordan
import MovingSofa.ForMathlib.MeasureTheory.Hausdorff.Arclength

/-!
# Boundary length of a rectifiable Jordan loop

Split the loop into two injective compact arcs. Their intersection consists of the endpoints
and is Hausdorff-null. Additivity of variation and Hausdorff measure identifies boundary
length with total variation for the original continuous parametrization.
-/

noncomputable section

open Set MeasureTheory MeasureTheory.Measure

namespace Isoperimetric

variable {γ : ℝ → Plane}

/-- A closed simple loop has Hausdorff length equal to its total variation.
The two injective arcs meet only at their endpoints, a Hausdorff-null set. -/
theorem RectifiableJordan.hausdorffMeasure_trace (h : RectifiableJordan γ) :
    hausdorffMeasure 1 (trace γ) = eVariationOn γ (Icc 0 1) := by
  let A := γ '' Icc 0 (1 / 2 : ℝ)
  let B := γ '' Icc (1 / 2 : ℝ) 1
  have hsubA : Icc (0 : ℝ) (1 / 2) ⊆ Icc 0 1 := Icc_subset_Icc le_rfl (by norm_num)
  have hsubB : Icc (1 / 2 : ℝ) 1 ⊆ Icc 0 1 := Icc_subset_Icc (by norm_num) le_rfl
  have hinjA : InjOn γ (Icc 0 (1 / 2 : ℝ)) :=
    h.injectiveOn.mono (by
      intro x hx
      exact ⟨hx.1, hx.2.trans_lt (by norm_num)⟩)
  have hinjB : InjOn γ (Icc (1 / 2 : ℝ) 1) := by
    intro s hs t ht heq
    rcases h.eq_or_endpoints (hsubB hs) (hsubB ht) heq with he | ⟨he, _⟩ | ⟨_, he⟩
    · exact he
    · linarith [hs.1]
    · linarith [ht.1]
  have hA : hausdorffMeasure 1 A = eVariationOn γ (Icc 0 (1 / 2 : ℝ)) :=
    hausdorffMeasure_image_Icc_eq_eVariationOn γ (by norm_num)
      (h.continuousOn.mono hsubA) hinjA (h.boundedVariationOn.mono hsubA)
  have hB : hausdorffMeasure 1 B = eVariationOn γ (Icc (1 / 2 : ℝ) 1) :=
    hausdorffMeasure_image_Icc_eq_eVariationOn γ (by norm_num)
      (h.continuousOn.mono hsubB) hinjB (h.boundedVariationOn.mono hsubB)
  have hmeet : A ∩ B ⊆ {γ 0} ∪ {γ (1 / 2)} := by
    rintro p ⟨⟨s, hs, hsp⟩, ⟨t, ht, htp⟩⟩
    rcases h.eq_or_endpoints (hsubA hs) (hsubB ht) (hsp.trans htp.symm) with
      he | ⟨hs0, _⟩ | ⟨hs1, _⟩
    · have hsHalf : s = 1 / 2 := by linarith [hs.2, ht.1]
      exact Or.inr (mem_singleton_iff.mpr (hsp.symm.trans (congrArg γ hsHalf)))
    · exact Or.inl (mem_singleton_iff.mpr (hsp.symm.trans (congrArg γ hs0)))
    · linarith [hs.2]
  let : NullSingletonClass (hausdorffMeasure 1 : Measure Plane) :=
    nullSingletonClass_hausdorff Plane (by norm_num : (0 : ℝ) < 1)
  have hnull : hausdorffMeasure 1 (A ∩ B) = 0 :=
    measure_mono_null hmeet (measure_union_null (measure_singleton _) (measure_singleton _))
  have hBm : MeasurableSet B :=
    (isCompact_Icc.image_of_continuousOn (h.continuousOn.mono hsubB)).measurableSet
  have hunion : A ∪ B = trace γ := by
    dsimp [A, B, trace]
    rw [← image_union, Icc_union_Icc_eq_Icc (by norm_num) (by norm_num)]
  have hsum : eVariationOn γ (Icc 0 (1 / 2 : ℝ)) +
      eVariationOn γ (Icc (1 / 2 : ℝ) 1) = eVariationOn γ (Icc 0 1) := by
    simpa using eVariationOn.Icc_add_Icc γ (s := univ)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1) (mem_univ _)
  rw [← hunion, measure_union₀ hBm.nullMeasurableSet hnull, hA, hB, hsum]

end Isoperimetric
