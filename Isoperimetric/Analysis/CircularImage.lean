import Isoperimetric.Analysis.RotationalODE

noncomputable section

open Set MeasureTheory Filter Complex
open scoped Real Interval

namespace Isoperimetric

private theorem exp_real_periodic :
    Function.Periodic (fun θ : ℝ ↦ Complex.exp ((θ : ℂ) * I)) (2 * Real.pi) := by
  intro θ
  simp [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.ofReal_mul,
    Complex.exp_two_pi_mul_I]

/-- A full positive or negative revolution covers the unit circle. -/
theorem exp_fullTurn_image (ε : ℝ) (hε : ε ^ 2 = 1) :
    (fun t : ℝ ↦ Complex.exp (((ε * (2 * Real.pi) * t : ℝ) : ℂ) * I)) '' Icc 0 1 =
      Metric.sphere (0 : ℂ) 1 := by
  rcases sq_eq_one_iff.mp hε with rfl | rfl
  · have hφ : (fun t : ℝ ↦ (2 * Real.pi) * t) '' Icc 0 1 = Icc 0 (2 * Real.pi) := by
      simpa using (continuous_const.mul continuous_id).continuousOn.image_Icc_of_monotoneOn
        (by norm_num : (0 : ℝ) ≤ 1)
        (fun x _ y _ hxy ↦ mul_le_mul_of_nonneg_left hxy (by positivity : 0 ≤ 2 * Real.pi))
    simp only [one_mul]
    change ((fun θ : ℝ ↦ Complex.exp ((θ : ℂ) * I)) ∘ (fun t : ℝ ↦ (2 * Real.pi) * t)) '' Icc 0 1 = _
    rw [image_comp, hφ]
    have hperiod := exp_real_periodic.image_Icc (a := 0) (by positivity : 0 < 2 * Real.pi)
    simpa using hperiod.trans Complex.range_exp_mul_I
  · have hφ : (fun t : ℝ ↦ -(2 * Real.pi) * t) '' Icc 0 1 = Icc (-(2 * Real.pi)) 0 := by
      simpa using (continuous_const.mul continuous_id).continuousOn.image_Icc_of_antitoneOn
        (by norm_num : (0 : ℝ) ≤ 1)
        (fun x _ y _ hxy ↦ mul_le_mul_of_nonpos_left hxy
          (neg_nonpos.mpr (by positivity : 0 ≤ 2 * Real.pi)))
    simp only [neg_one_mul]
    change ((fun θ : ℝ ↦ Complex.exp ((θ : ℂ) * I)) ∘ (fun t : ℝ ↦ -(2 * Real.pi) * t)) '' Icc 0 1 = _
    rw [image_comp, hφ]
    have hperiod := exp_real_periodic.image_Icc (a := -(2 * Real.pi)) (by positivity : 0 < 2 * Real.pi)
    simpa using hperiod.trans Complex.range_exp_mul_I

variable {γ : ℝ → Plane}

/-- The ODE's amplitude cannot vanish for a Jordan once-traversal. -/
theorem RectifiableJordan.rotational_amplitude_pos (h : RectifiableJordan γ) (c : Plane) (ω : ℝ)
    (hode : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      deriv (arclengthParam γ) t = ω • quarterTurn (arclengthParam γ t - c)) :
    0 < ‖arclengthParam γ 0 - c‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have hsol := h.solve_rotational_ode c ω hode
  have hh := hsol (1 / 2) (by norm_num)
  rw [hz, map_zero, mul_zero] at hh
  have hhalf : arclengthParam γ (1 / 2) - c = 0 := planeComplex.injective (hh.trans (map_zero _).symm)
  have heq : arclengthParam γ 0 = arclengthParam γ (1 / 2) :=
    (sub_eq_zero.mp hz).trans (sub_eq_zero.mp hhalf).symm
  have ht := h.arclengthParam_isRectifiableJordan.injectiveOn
    (by norm_num : (0 : ℝ) ∈ Ico 0 1) (by norm_num : (1 / 2 : ℝ) ∈ Ico 0 1) heq
  norm_num at ht

/-- A Jordan loop solving the full-turn ODE has exactly a positive-radius circle image. -/
theorem RectifiableJordan.trace_eq_sphere_of_rotational_ode (h : RectifiableJordan γ)
    (c : Plane) (ε : ℝ) (hε : ε ^ 2 = 1)
    (hode : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      deriv (arclengthParam γ) t =
        (ε * (2 * Real.pi)) • quarterTurn (arclengthParam γ t - c)) :
    trace γ = Metric.sphere c ‖arclengthParam γ 0 - c‖ := by
  let η := arclengthParam γ
  let a := planeComplex (η 0 - c)
  have hsol := h.solve_rotational_ode c (ε * (2 * Real.pi)) hode
  have hr := h.rotational_amplitude_pos c (ε * (2 * Real.pi)) hode
  have ha : a ≠ 0 := by
    intro ha0
    have hzero : η 0 - c = 0 := planeComplex.injective (ha0.trans (map_zero _).symm)
    exact hr.ne' (by rw [hzero, norm_zero])
  rw [← h.trace_arclengthParam]
  apply Subset.antisymm
  · rintro p ⟨t, ht, rfl⟩
    rw [Metric.mem_sphere, dist_eq_norm]
    rw [← planeComplex.norm_map (η t - c), hsol t ht, norm_mul,
      Complex.norm_exp_ofReal_mul_I, one_mul, planeComplex.norm_map]
  · intro p hp
    have hpnorm : ‖p - c‖ = ‖η 0 - c‖ := by simpa [Metric.mem_sphere, dist_eq_norm] using hp
    have hu : planeComplex (p - c) / a ∈ Metric.sphere (0 : ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_div]
      dsimp [a]
      rw [planeComplex.norm_map, planeComplex.norm_map, hpnorm, div_self hr.ne']
    obtain ⟨t, ht, htu⟩ := (exp_fullTurn_image ε hε).symm.subset hu
    dsimp only at htu
    refine ⟨t, ht, ?_⟩
    have heq : planeComplex (η t - c) = planeComplex (p - c) := by
      rw [hsol t ht, htu]
      exact div_mul_cancel₀ _ ha
    exact sub_left_inj.mp (planeComplex.injective heq)

/-- Analytic rigidity at signed-area equality, without smoothness assumptions. -/
theorem RectifiableJordan.circle_of_signedArea_equality (h : RectifiableJordan γ)
    (ε : ℝ) (hε : ε ^ 2 = 1)
    (heq : length γ ^ 2 = 4 * Real.pi * ε *
      MovingSofa.curveAreaFunctional h.arclengthParam_isRectifiableJordan.bvPath) :
    ∃ (c : Plane) (r : ℝ), 0 < r ∧ trace γ = Metric.sphere c r := by
  have hode := h.rotational_ode_of_signedArea_equality ε hε heq
  exact ⟨arclengthMean γ, ‖arclengthParam γ 0 - arclengthMean γ‖,
    h.rotational_amplitude_pos _ _ hode, h.trace_eq_sphere_of_rotational_ode _ ε hε hode⟩

end Isoperimetric
