import Isoperimetric.Analysis.Rotation
import Isoperimetric.Energy

noncomputable section

open Set MeasureTheory Filter Complex
open scoped Topology

namespace Isoperimetric

variable {γ : ℝ → Plane}

/-- Every rectifiable Jordan loop has an interior arclength parameter with nonzero velocity. -/
theorem RectifiableJordan.exists_regular_parameter (h : RectifiableJordan γ) :
    ∃ t ∈ Ioo (0 : ℝ) 1, ∃ v : Plane,
      HasDerivAt (arclengthParam γ) v t ∧ ‖v‖ = length γ := by
  have hd := h.lipschitzOnWith_arclengthParam.ae_differentiableWithinAt (μ := volume) measurableSet_Icc
  have hn := h.norm_deriv_arclengthParam_ae
  rw [← restrict_Ioo_eq_restrict_Icc] at hd hn
  have ha : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      HasDerivAt (arclengthParam γ) (deriv (arclengthParam γ) t) t ∧
        ‖deriv (arclengthParam γ) t‖ = length γ := by
    filter_upwards [hd, hn, ae_restrict_mem measurableSet_Ioo] with t hdt hnt ht
    exact ⟨(hdt.differentiableAt (Icc_mem_nhds ht.1 ht.2)).hasDerivAt, hnt⟩
  obtain ⟨t, ht, hdt, hnt⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (μ := volume) (s := Ioo (0 : ℝ) 1) (by simp) ha
  exact ⟨t, ht, deriv (arclengthParam γ) t, hdt, hnt⟩

/-- Near a regular parameter, projection along its velocity has positive secant slope. -/
theorem positive_secant_near_regular_parameter {η : ℝ → Plane} {t : ℝ} {v : Plane}
    (hd : HasDerivAt η v t) (hv : v ≠ 0) :
    ∃ δ > 0, ∀ s : ℝ, |s - t| < δ → s ≠ t →
      0 < (planeComplex (η s - η t) / planeComplex v).re / (s - t) := by
  let z : ℝ → ℂ := fun s ↦ planeComplex (η s - η t) / planeComplex v
  have hvC : planeComplex v ≠ 0 := fun hz ↦ hv (planeComplex.injective (hz.trans (map_zero _).symm))
  have hzD : HasDerivAt z 1 t := by
    have hD := (planeComplex.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      (hd.sub_const (η t))).div_const (planeComplex v)
    change HasDerivAt z (planeComplex v / planeComplex v) t at hD
    rwa [div_self hvC] at hD
  have hfD : HasDerivAt (fun s ↦ (z s).re) 1 t :=
    (reCLM.hasFDerivAt.comp_hasDerivAt t hzD)
  have hf0 : (z t).re = 0 := by simp [z]
  have he : ∀ᶠ s in 𝓝[≠] t, 0 < slope (fun s ↦ (z s).re) t s :=
    hfD.tendsto_slope.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at he
  obtain ⟨δ, hδ, hclose⟩ := he
  refine ⟨δ, hδ, ?_⟩
  intro s hs hst
  have hp := hclose (y := s) (by simpa only [Real.dist_eq] using hs) hst
  simpa only [slope_def_field, hf0, sub_zero] using hp

/-- Compactness and simplicity turn a local regular-parameter statement into
a spatial neighborhood that sees only that parameter window. -/
theorem RectifiableJordan.exists_spatial_neighborhood_of_parameter_window (h : RectifiableJordan γ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ > 0, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖arclengthParam γ s - arclengthParam γ t‖ < ρ → |s - t| < δ := by
  let K := Icc (0 : ℝ) 1 \ Ioo (t - δ) (t + δ)
  have hK : IsCompact K := isCompact_Icc.diff isOpen_Ioo
  have hc := h.arclengthParam_isRectifiableJordan
  have hKim : IsCompact (arclengthParam γ '' K) := hK.image_of_continuousOn
    (hc.continuousOn.mono sdiff_subset)
  have hnot : arclengthParam γ t ∉ arclengthParam γ '' K := by
    rintro ⟨s, hs, hst⟩
    have hs01 : s ∈ Icc (0 : ℝ) 1 := hs.1
    rcases hc.eq_or_endpoints hs01 ⟨ht.1.le, ht.2.le⟩ hst with heq | ⟨_, ht1⟩ | ⟨_, ht0⟩
    · subst s
      exact hs.2 ⟨by linarith, by linarith⟩
    · exact ht.2.ne ht1
    · exact ht.1.ne' ht0
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hKim.isClosed.isOpen_compl _ hnot
  refine ⟨ρ, hρ, ?_⟩
  intro s hs hnear
  by_contra hfar
  have hsK : s ∈ K := by
    refine ⟨hs, ?_⟩
    intro hwin
    apply hfar
    rw [abs_lt]
    constructor <;> linarith [hwin.1, hwin.2]
  exact (hball (by simpa [Metric.mem_ball, dist_eq_norm] using hnear)) ⟨s, hsK, rfl⟩

/-- A short normal segment through a regular arclength point meets the loop only there. -/
theorem RectifiableJordan.exists_normal_crosscut (h : RectifiableJordan γ) :
    ∃ t ∈ Ioo (0 : ℝ) 1, ∃ v : Plane, v ≠ 0 ∧
      HasDerivAt (arclengthParam γ) v t ∧ ∃ α > 0,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ u : ℝ, |u| < α →
        arclengthParam γ s = arclengthParam γ t + u • quarterTurn v → s = t ∧ u = 0 := by
  obtain ⟨t, ht, v, hd, hn⟩ := h.exists_regular_parameter
  have hv : v ≠ 0 := by
    intro heq
    have := h.length_pos
    simp [heq] at hn
    linarith
  obtain ⟨δ, hδ, hsec⟩ := positive_secant_near_regular_parameter hd hv
  obtain ⟨ρ, hρ, hnear⟩ := h.exists_spatial_neighborhood_of_parameter_window ht hδ
  have hnpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  refine ⟨t, ht, v, hv, hd, ρ / ‖v‖, div_pos hρ hnpos, ?_⟩
  intro s hs u hu heq
  have hdiff : arclengthParam γ s - arclengthParam γ t = u • quarterTurn v := by
    rw [heq, add_sub_cancel_left]
  have hclose : ‖arclengthParam γ s - arclengthParam γ t‖ < ρ := by
    rw [hdiff, norm_smul, Real.norm_eq_abs, norm_quarterTurn]
    exact (lt_div_iff₀ hnpos).mp hu
  have hvC : planeComplex v ≠ 0 := fun hz ↦ hv (planeComplex.injective (hz.trans (map_zero _).symm))
  have hproject : (planeComplex (arclengthParam γ s - arclengthParam γ t) /
      planeComplex v).re = 0 := by
    rw [hdiff, map_smul, planeComplex_quarterTurn, Complex.real_smul]
    have he : (u : ℂ) * (I * planeComplex v) / planeComplex v = (u : ℂ) * I := by
      field_simp
    rw [he]
    simp
  have hst : s = t := by
    by_contra hne
    have hp := hsec s (hnear s hs hclose) hne
    rw [hproject, zero_div] at hp
    exact lt_irrefl _ hp
  refine ⟨hst, ?_⟩
  have hzero : u • quarterTurn v = 0 := by simpa [hst] using hdiff.symm
  rcases smul_eq_zero.mp hzero with hu0 | hv0
  · exact hu0
  · have hnorm := congrArg norm hv0
    rw [norm_quarterTurn, norm_zero] at hnorm
    exact False.elim (hv (norm_eq_zero.mp hnorm))

end Isoperimetric
