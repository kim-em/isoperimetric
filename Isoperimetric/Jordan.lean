import Isoperimetric.Statement
import MovingSofa.Curve.Jordan.Interior
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

noncomputable section

open Set MeasureTheory

namespace Isoperimetric

variable {γ : ℝ → Plane}

theorem RectifiableJordan.trace_eq_image_Ico (h : RectifiableJordan γ) :
    trace γ = γ '' Ico 0 1 := by
  apply Subset.antisymm
  · rintro p ⟨t, ht, rfl⟩
    rcases ht.2.eq_or_lt with rfl | ht1
    · exact ⟨0, by norm_num, h.closed⟩
    · exact ⟨t, ⟨ht.1, ht1⟩, rfl⟩
  · exact image_mono Ico_subset_Icc_self

/-- The interval hypotheses imply the usual circle-based Jordan-curve definition. -/
theorem RectifiableJordan.isJordanCurve (h : RectifiableJordan γ) :
    MovingSofa.IsJordanCurve (trace γ) := by
  let : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let f : AddCircle (1 : ℝ) → Plane := AddCircle.liftIco 1 0 γ
  have hfc : Continuous f := AddCircle.liftIco_zero_continuous h.closed h.continuousOn
  have hfi : Function.Injective f := by
    intro s t hst
    apply (AddCircle.equivIco (1 : ℝ) 0).injective
    apply Subtype.ext
    exact h.injectiveOn
      (by simpa using (AddCircle.equivIco (1 : ℝ) 0 s).property)
      (by simpa using (AddCircle.equivIco (1 : ℝ) 0 t).property) hst
  have hfr : range f = trace γ := by
    rw [h.trace_eq_image_Ico]
    apply Subset.antisymm
    · rintro p ⟨s, rfl⟩
      exact ⟨AddCircle.equivIco (1 : ℝ) 0 s,
        by simpa using (AddCircle.equivIco (1 : ℝ) 0 s).property, rfl⟩
    · rintro p ⟨t, ht, rfl⟩
      exact ⟨(t : AddCircle (1 : ℝ)), AddCircle.liftIco_zero_coe_apply ht⟩
  let e : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  refine ⟨f ∘ e.symm, hfc.comp e.symm.continuous, hfi.comp e.symm.injective, ?_⟩
  rw [range_comp, e.symm.surjective.range_eq, image_univ, hfr]

theorem RectifiableJordan.isCompact_trace (h : RectifiableJordan γ) :
    IsCompact (trace γ) := isCompact_Icc.image_of_continuousOn h.continuousOn

/-- The set used to define area is the bounded open Jordan component. -/
theorem RectifiableJordan.enclosed_properties (h : RectifiableJordan γ) :
    IsOpen (enclosed γ) ∧ IsConnected (enclosed γ) ∧
      Bornology.IsBounded (enclosed γ) := by
  obtain ⟨U, V, hUo, _, hUc, _, hUb, hVb, _, hcover, _, _, hUcomp, hVcomp⟩ :=
    MovingSofa.jordan_separation h.isJordanCurve
  have heq : enclosed γ = U := by
    ext p
    change (p ∉ trace γ ∧ Bornology.IsBounded (connectedComponentIn (trace γ)ᶜ p)) ↔ p ∈ U
    constructor
    · rintro ⟨hp, hb⟩
      rcases hcover.symm.subset hp with hpU | hpV
      · exact hpU
      · exact False.elim (hVb ((hVcomp p hpV) ▸ hb))
    · intro hp
      have hpcom : p ∈ (trace γ)ᶜ := hcover ▸ mem_union_left V hp
      refine ⟨hpcom, ?_⟩
      rw [hUcomp p hp]
      exact hUb
  rw [heq]
  exact ⟨hUo, hUc, hUb⟩

theorem RectifiableJordan.measurableSet_enclosed (h : RectifiableJordan γ) :
    MeasurableSet (enclosed γ) := h.enclosed_properties.1.measurableSet

theorem RectifiableJordan.volume_enclosed_ne_top (h : RectifiableJordan γ) :
    volume (enclosed γ) ≠ ⊤ := h.enclosed_properties.2.2.measure_lt_top.ne

theorem RectifiableJordan.frontier_enclosed (h : RectifiableJordan γ) :
    frontier (enclosed γ) = trace γ := h.isJordanCurve.frontier_jordanInterior

theorem RectifiableJordan.eVariationOn_ne_top (h : RectifiableJordan γ) :
    eVariationOn γ (Icc 0 1) ≠ ⊤ := h.boundedVariationOn

/-- The only repeated point of a once-traversal is the pair of endpoints. -/
theorem RectifiableJordan.eq_or_endpoints (h : RectifiableJordan γ)
    {s t : ℝ} (hs : s ∈ Icc 0 1) (ht : t ∈ Icc 0 1) (heq : γ s = γ t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  by_cases hs1 : s = 1
  · subst s
    by_cases ht1 : t = 1
    · exact Or.inl ht1.symm
    · have ht0 : t = 0 := h.injectiveOn ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩
        (by norm_num) (heq.symm.trans h.closed.symm)
      exact Or.inr (Or.inr ⟨rfl, ht0⟩)
  · by_cases ht1 : t = 1
    · subst t
      have hs0 : s = 0 := h.injectiveOn ⟨hs.1, lt_of_le_of_ne hs.2 hs1⟩
        (by norm_num) (heq.trans h.closed.symm)
      exact Or.inr (Or.inl ⟨hs0, rfl⟩)
    · exact Or.inl (h.injectiveOn ⟨hs.1, lt_of_le_of_ne hs.2 hs1⟩
        ⟨ht.1, lt_of_le_of_ne ht.2 ht1⟩ heq)

theorem RectifiableJordan.length_pos (h : RectifiableJordan γ) : 0 < length γ := by
  have hne : γ 0 ≠ γ (1 / 2) := by
    intro heq
    have := h.injectiveOn (by norm_num : (0 : ℝ) ∈ Ico 0 1)
      (by norm_num : (1 / 2 : ℝ) ∈ Ico 0 1) heq
    norm_num at this
  have hv : 0 < eVariationOn γ (Icc 0 1) :=
    (edist_pos.mpr hne).trans_le (eVariationOn.edist_le γ
      (by norm_num : (0 : ℝ) ∈ Icc 0 1)
      (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1))
  exact ENNReal.toReal_pos hv.ne' h.eVariationOn_ne_top

end Isoperimetric
