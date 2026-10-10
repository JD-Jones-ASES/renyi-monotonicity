module

public import RenyiMonotonicity.FairBoundary
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

namespace RenyiMonotonicity

open Set

/-- Positive mixed derivative propagates the nonpositive hyperbolic normal
strictly into the region below the hyperbola. -/
theorem fairCorrectedKernel_derivative_neg (q x y : ℝ)
    (hq₀ : 0 < q) (hq₁ : q < 1) (hx : 0 < x) (hy : 0 ≤ y) (hxy : x * y < 1) :
    fairKernelDerivativeX q x y + fairCorrectionDerivative q x < 0 := by
  have hix : 0 < x⁻¹ := inv_pos.mpr hx
  have hyx : y < x⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hx]
    nlinarith
  have hm : StrictMonoOn (fairKernelDerivativeX q x) (Icc 0 x⁻¹) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro t ht
      exact (hasDerivAt_fairKernelDerivativeX_y q x t
        (by unfold fairAverage; linarith [ht.1])).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hA : 0 < fairAverage x t := by unfold fairAverage; linarith [ht.1]
      rw [(hasDerivAt_fairKernelDerivativeX_y q x t hA).deriv]
      apply fairKernelMixedDerivative_pos q x t hq₀ hq₁ hx.le ht.1.le
      have hh := mul_lt_mul_of_pos_left ht.2 hx
      simpa [mul_inv_cancel₀ hx.ne'] using hh
  have hh := hm ⟨hy, hyx.le⟩ ⟨hix.le, le_rfl⟩ hyx
  have hb := fair_boundary_normal_nonpos q x hq₀.ne' hx
  linarith

/-- Differentiation of the corrected local term includes the removable point. -/
theorem hasDerivAt_fairCorrectedKernel_x (q x y : ℝ)
    (hq : q ≠ 0) (hx : 0 < x) (hy : 0 ≤ y) :
    HasDerivAt (fun t => fairCorrectedKernel q t y)
      (fairKernelDerivativeX q x y + fairCorrectionDerivative q x) x := by
  exact ((hasDerivAt_fairKernel_x q x y
    (by unfold fairAverage; linarith)).add
    (hasDerivAt_fairCorrection q x hq hx)).add_const _

/-- Continuity at zero is retained; the scalar correction was extended there. -/
theorem continuousOn_fairCorrectedKernel_x (q y : ℝ) (hq : 0 < q) (hy : 0 ≤ y) :
    ContinuousOn (fun x => fairCorrectedKernel q x y) (Ici 0) := by
  apply ContinuousOn.add
  · apply ContinuousOn.add
    · intro x hx
      exact (hasDerivAt_fairKernel_x q x y
        (by unfold fairAverage; have := hx; change 0 ≤ x at this; linarith)).continuousAt.continuousWithinAt
    · exact continuousOn_fairCorrection q hq
  · exact continuousOn_const

/-- A positive opposite coordinate gives strict local positivity, including a
zero first coordinate. -/
theorem fairCorrectedKernel_pos_of_right_pos (q x y : ℝ)
    (hq₀ : 0 < q) (hq₁ : q < 1) (hx : 0 ≤ x) (hy : 0 < y) (hxy : x * y < 1) :
    0 < fairCorrectedKernel q x y := by
  have hiy : 0 < y⁻¹ := inv_pos.mpr hy
  have hxi : x < y⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hy]
    exact hxy
  have hm : StrictAntiOn (fun t => fairCorrectedKernel q t y) (Icc 0 y⁻¹) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · exact (continuousOn_fairCorrectedKernel_x q y hq₀ hy.le).mono Icc_subset_Ici_self
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hasDerivAt_fairCorrectedKernel_x q t y hq₀.ne' ht.1 hy.le).deriv]
      apply fairCorrectedKernel_derivative_neg q t y hq₀ hq₁ ht.1 hy.le
      have hh := mul_lt_mul_of_pos_right ht.2 hy
      simpa [inv_mul_cancel₀ hy.ne'] using hh
  have hh := hm ⟨hx, hxi.le⟩ ⟨hiy.le, le_rfl⟩ hxi
  have hb : fairCorrectedKernel q y⁻¹ y = 0 := by
    simpa using fairCorrectedKernel_boundary q y⁻¹ hq₀.ne' hiy
  simpa [hb] using hh

/-- Strict local inequality on the closed nonnegative quadrant below the
hyperbola, including both zero-edge cases. -/
theorem fairCorrectedKernel_pos (q x y : ℝ)
    (hq₀ : 0 < q) (hq₁ : q < 1) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x * y < 1) :
    0 < fairCorrectedKernel q x y := by
  rcases lt_or_eq_of_le hy with hy | rfl
  · exact fairCorrectedKernel_pos_of_right_pos q x y hq₀ hq₁ hx hy hxy
  rcases lt_or_eq_of_le hx with hx | rfl
  · rw [fairCorrectedKernel_symm]
    exact fairCorrectedKernel_pos_of_right_pos q 0 x hq₀ hq₁ (by norm_num) hx (by simp)
  have hm : StrictAntiOn (fun t => fairCorrectedKernel q t 0) (Icc 0 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · exact (continuousOn_fairCorrectedKernel_x q 0 hq₀ (by norm_num)).mono Icc_subset_Ici_self
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hasDerivAt_fairCorrectedKernel_x q t 0 hq₀.ne' ht.1 (by norm_num)).deriv]
      exact fairCorrectedKernel_derivative_neg q t 0 hq₀ hq₁ ht.1 (by norm_num) (by simp)
  have hh := hm (show (0 : ℝ) ∈ Icc 0 1 by simp) (show (1 : ℝ) ∈ Icc 0 1 by simp) zero_lt_one
  have hp : 0 < fairCorrectedKernel q 1 0 := by
    rw [fairCorrectedKernel_symm]
    exact fairCorrectedKernel_pos_of_right_pos q 0 1 hq₀ hq₁ (by norm_num) zero_lt_one (by simp)
  exact hp.trans hh

/-- Nonstrict version, with exact equality on the hyperbolic boundary. -/
theorem fairCorrectedKernel_nonneg (q x y : ℝ)
    (hq₀ : 0 < q) (hq₁ : q < 1) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x * y ≤ 1) :
    0 ≤ fairCorrectedKernel q x y := by
  rcases lt_or_eq_of_le hxy with hxy | hxy
  · exact (fairCorrectedKernel_pos q x y hq₀ hq₁ hx hy hxy).le
  have hx₀ : 0 < x := by nlinarith
  have he : y = x⁻¹ := by
    apply (mul_left_cancel₀ hx₀.ne')
    rw [mul_inv_cancel₀ hx₀.ne']
    exact hxy
  rw [he, fairCorrectedKernel_boundary q x hq₀.ne' hx₀]

end RenyiMonotonicity
