import Isoperimetric.Main

/-!
Check the public theorem against a statement written entirely with Mathlib objects.
The expected hypotheses and conclusion do not use the project's curve predicate,
trace, area, length, or interior definitions. Changing their mathematical meaning
must therefore satisfy this independent formulation as well.
-/

noncomputable section

open Set MeasureTheory

example (γ : ℝ → EuclideanSpace ℝ (Fin 2))
    (hcontinuous : ContinuousOn γ (Icc 0 1)) (hclosed : γ 0 = γ 1)
    (hsimple : InjOn γ (Ico 0 1)) (hrectifiable : BoundedVariationOn γ (Icc 0 1)) :
    let C := γ '' Icc (0 : ℝ) 1
    let A := (volume {p | p ∉ C ∧ Bornology.IsBounded (connectedComponentIn Cᶜ p)}).toReal
    let L := (eVariationOn γ (Icc (0 : ℝ) 1)).toReal
    4 * Real.pi * A ≤ L ^ 2 ∧
      (4 * Real.pi * A = L ^ 2 ↔
        ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ), 0 < r ∧ C = Metric.sphere c r) :=
  Isoperimetric.classical_isoperimetric γ hcontinuous hclosed hsimple hrectifiable

example (γ : ℝ → EuclideanSpace ℝ (Fin 2))
    (hcontinuous : ContinuousOn γ (Icc 0 1)) (hclosed : γ 0 = γ 1)
    (hsimple : InjOn γ (Ico 0 1)) (hrectifiable : BoundedVariationOn γ (Icc 0 1)) :
    let C := γ '' Icc (0 : ℝ) 1
    volume {p | p ∉ C ∧ Bornology.IsBounded (connectedComponentIn Cᶜ p)} ≠ ⊤ ∧
      eVariationOn γ (Icc (0 : ℝ) 1) ≠ ⊤ ∧
      0 < (eVariationOn γ (Icc (0 : ℝ) 1)).toReal := by
  let h : Isoperimetric.RectifiableJordan γ := ⟨hcontinuous, hclosed, hsimple, hrectifiable⟩
  exact ⟨h.volume_enclosed_ne_top, h.eVariationOn_ne_top, h.length_pos⟩
