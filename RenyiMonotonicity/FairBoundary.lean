module

public import RenyiMonotonicity.FairKernel

@[expose] public section

namespace RenyiMonotonicity

noncomputable def fairBoundaryScale (q x : ℝ) : ℝ :=
  (2 : ℝ) ^ (-q) * (x + 1) ^ (2 * q - 3) * x ^ (1 - q)

theorem fairBoundaryScale_pos (q x : ℝ) (hx : 0 < x) : 0 < fairBoundaryScale q x := by
  unfold fairBoundaryScale
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.rpow_pos_of_pos (by linarith) _)) (Real.rpow_pos_of_pos hx _)

/-- Real powers of the hyperbolic boundary average, with positive bases verified. -/
theorem fairAverage_boundary_rpow (x t : ℝ) (hx : 0 < x) :
    fairAverage x x⁻¹ ^ t = (x + 1) ^ (2 * t) / ((2 : ℝ) ^ t * x ^ t) := by
  have he : fairAverage x x⁻¹ = (x + 1) ^ 2 / (2 * x) := by
    unfold fairAverage
    field_simp
    ring
  rw [he, Real.div_rpow (sq_nonneg _) (by positivity),
    Real.mul_rpow (by norm_num) hx.le]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ x + 1)]
  norm_num

/-- Normalization of the power appearing in the boundary first derivative. -/
theorem fairAverage_boundary_rpow_three (q x : ℝ) (hx : 0 < x) :
    fairAverage x x⁻¹ ^ (q - 3) = fairBoundaryScale q x * (8 * x ^ 2 / (x + 1) ^ 3) := by
  have hp : 0 < x + 1 := by linarith
  rw [fairAverage_boundary_rpow x (q - 3) hx,
    show 2 * (q - 3) = (2 * q - 3) - (3 : ℕ) by push_cast; ring,
    Real.rpow_sub_natCast hp.ne', Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
    Real.rpow_sub hx]
  unfold fairBoundaryScale
  rw [Real.rpow_neg (by norm_num), Real.rpow_sub hx, Real.rpow_one]
  norm_num
  field_simp

/-- The actual first derivative of the local kernel at the hyperbola has this
rational normal form after factoring its positive scale. -/
theorem fairKernelDerivativeX_boundary (q x : ℝ) (hx : 0 < x) :
    fairKernelDerivativeX q x x⁻¹ = fairBoundaryScale q x *
      ((2 * (-q * x ^ 2 + q - 2) - q * (q - 2) * (x - 1) ^ 2) / (x + 1)) := by
  unfold fairKernelDerivativeX
  rw [fairAverage_boundary_rpow_three q x hx]
  unfold fairAverage fairNumerator
  field_simp
  ring

/-- The actual scalar correction derivative in the same positive normalization. -/
theorem fairCorrectionRegularDerivative_boundary (q x : ℝ) (hq : q ≠ 0)
    (hx : 0 < x) (hx₁ : x ≠ 1) :
    fairCorrectionRegularDerivative q x = fairBoundaryScale q x *
      (q * x ^ q * (x - 1) *
        (x * (2 * (x + 1) + (x - 1) * (2 * q - 2)) * (x ^ q - 1) -
          (x ^ 2 - 1) * q * x ^ q) / (x ^ 2 * (x ^ q - 1) ^ 2)) := by
  have hU : x ^ q ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx q)
  have hUm : x ^ q - 1 ≠ 0 := by
    intro h
    exact hx₁ ((Real.rpow_left_inj hx.le zero_le_one hq).mp (by simpa using sub_eq_zero.mp h))
  unfold fairCorrectionRegularDerivative fairBoundaryScale
  rw [Real.rpow_sub_one hx.ne', Real.rpow_sub hx, Real.rpow_one]
  field_simp
  ring

/-- The exact boundary normal derivative is a negative square times a positive scale. -/
theorem fair_boundary_normal_square (q x : ℝ) (hq : q ≠ 0)
    (hx : 0 < x) (hx₁ : x ≠ 1) :
    fairKernelDerivativeX q x x⁻¹ + fairCorrectionDerivative q x =
      -fairBoundaryScale q x *
        (x ^ q * q * x - x ^ q * q - 2 * x ^ q * x + q * x ^ 2 - q * x + 2 * x) ^ 2 /
        (x ^ 2 * (x ^ q - 1) ^ 2 * (x + 1)) := by
  have hU : x ^ q ≠ 1 := by
    intro h
    exact hx₁ ((Real.rpow_left_inj hx.le zero_le_one hq).mp (by simpa using h))
  rw [fairCorrectionDerivative, ite_eq_right hx₁,
    fairKernelDerivativeX_boundary q x hx,
    fairCorrectionRegularDerivative_boundary q x hq hx hx₁, ← mul_add,
    fair_boundary_square_algebra q x (x ^ q) hx.ne' hU (by linarith)]
  ring

/-- The boundary normal derivative is nonpositive even at the removable point. -/
theorem fair_boundary_normal_nonpos (q x : ℝ) (hq : q ≠ 0) (hx : 0 < x) :
    fairKernelDerivativeX q x x⁻¹ + fairCorrectionDerivative q x ≤ 0 := by
  by_cases hx₁ : x = 1
  · subst x
    have hp : (2 : ℝ) ^ (q - 2) = (2 : ℝ) ^ (q - 3) * 2 := by
      rw [← Real.rpow_add_one (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      ring
    norm_num [fairKernelDerivativeX, fairAverage, fairNumerator, fairCorrectionDerivative, hp]
  · rw [fair_boundary_normal_square q x hq hx hx₁]
    have hs := fairBoundaryScale_pos q x hx
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) (sq_nonneg _))
      (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by linarith))

/-- Normalization of the power appearing in the boundary value. -/
theorem fairAverage_boundary_rpow_two (q x : ℝ) (hx : 0 < x) :
    fairAverage x x⁻¹ ^ (q - 2) = fairBoundaryScale q x * (4 * x / (x + 1)) := by
  have hp : 0 < x + 1 := by linarith
  rw [fairAverage_boundary_rpow x (q - 2) hx,
    show 2 * (q - 2) = (2 * q - 3) - (1 : ℕ) by push_cast; ring,
    Real.rpow_sub_natCast hp.ne', Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
    Real.rpow_sub hx]
  unfold fairBoundaryScale
  rw [Real.rpow_neg (by norm_num), Real.rpow_sub hx, Real.rpow_one]
  norm_num
  field_simp

/-- Corrected scalar term whose flux sums telescope. -/
noncomputable def fairCorrectedKernel (q x y : ℝ) : ℝ :=
  fairKernel q x y + fairCorrection q x + fairCorrection q y

theorem fairCorrectedKernel_symm (q x y : ℝ) :
    fairCorrectedKernel q x y = fairCorrectedKernel q y x := by
  unfold fairCorrectedKernel fairKernel fairNumerator fairAverage
  rw [show y + 2 + x = x + 2 + y by ring, show (y - x) ^ 2 = (x - y) ^ 2 by ring]
  ring

/-- Exact vanishing of the corrected local term on the entire positive hyperbola. -/
theorem fairCorrectedKernel_boundary (q x : ℝ) (hq : q ≠ 0) (hx : 0 < x) :
    fairCorrectedKernel q x x⁻¹ = 0 := by
  by_cases hx₁ : x = 1
  · subst x
    norm_num [fairCorrectedKernel, fairKernel, fairNumerator, fairAverage]
  have hU : x ^ q ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx q)
  have hUm : x ^ q - 1 ≠ 0 := by
    intro h
    exact hx₁ ((Real.rpow_left_inj hx.le zero_le_one hq).mp (by simpa using sub_eq_zero.mp h))
  have hf : fairCorrection q x⁻¹ = -fairCorrection q x / x ^ q := by
    apply (eq_div_iff hU).mpr
    simpa [mul_comm] using fairCorrection_reciprocal q x hq hx
  have hp : 0 < x + 1 := by linarith
  have hpow : (x + 1) ^ (2 * q - 2) = (x + 1) ^ (2 * q - 3) * (x + 1) := by
    rw [← Real.rpow_add_one hp.ne']
    congr 1
    ring
  unfold fairCorrectedKernel fairKernel
  rw [fairAverage_boundary_rpow_two q x hx, hf]
  unfold fairNumerator fairBoundaryScale fairCorrection
  rw [hpow, Real.rpow_sub hx, Real.rpow_one]
  field_simp
  ring

end RenyiMonotonicity
