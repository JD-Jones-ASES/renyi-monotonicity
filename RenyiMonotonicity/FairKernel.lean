module

public import RenyiMonotonicity.FairScalar

@[expose] public section

namespace RenyiMonotonicity

noncomputable def fairAverage (x y : ℝ) : ℝ := (x + 2 + y) / 2

noncomputable def fairNumerator (q x y : ℝ) : ℝ := 1 - x * y - q / 4 * (x - y) ^ 2

/-- The normalized local contribution to the fair-coordinate derivative. -/
noncomputable def fairKernel (q x y : ℝ) : ℝ :=
  fairNumerator q x y * fairAverage x y ^ (q - 2)

noncomputable def fairKernelDerivativeX (q x y : ℝ) : ℝ :=
  fairAverage x y ^ (q - 3) *
    ((-y - q / 2 * (x - y)) * fairAverage x y + (q - 2) / 2 * fairNumerator q x y)

/-- The mixed derivative has a sign visible directly from `xy≤1`. -/
noncomputable def fairKernelMixedDerivative (q x y : ℝ) : ℝ :=
  -((q - 2) * (q - 1)) / 16 * fairAverage x y ^ (q - 4) *
    ((q - 2) * (x - y) ^ 2 + 4 * x * y - 4)

/-- Exact first partial derivative. -/
theorem hasDerivAt_fairKernel_x (q x y : ℝ) (hA : 0 < fairAverage x y) :
    HasDerivAt (fun t => fairKernel q t y) (fairKernelDerivativeX q x y) x := by
  have hN : HasDerivAt (fun t => fairNumerator q t y) (-y - q / 2 * (x - y)) x := by
    have h := ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).mul_const y)).sub
      ((((hasDerivAt_id x).sub_const y).pow 2).const_mul (q / 4))
    convert h using 1
    · ext t
      simp [fairNumerator]
    · simp only [id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one, one_mul,
        zero_sub]
      ring
  have hA' : HasDerivAt (fun t => fairAverage t y) (1 / 2) x := by
    simpa [fairAverage] using (((hasDerivAt_id x).add_const 2).add_const y).div_const 2
  have h := hN.mul (hA'.rpow_const (p := q - 2) (Or.inl hA.ne'))
  convert h using 1
  · rfl
  · simp only [show q - 2 - 1 = q - 3 by ring]
    unfold fairKernelDerivativeX
    have hpow : fairAverage x y ^ (q - 2) = fairAverage x y ^ (q - 3) * fairAverage x y := by
      rw [← Real.rpow_add_one hA.ne']
      congr 1
      ring
    rw [hpow]
    ring

/-- Exact second mixed partial derivative, proved from the displayed scalar functions. -/
theorem hasDerivAt_fairKernelDerivativeX_y (q x y : ℝ) (hA : 0 < fairAverage x y) :
    HasDerivAt (fun t => fairKernelDerivativeX q x t) (fairKernelMixedDerivative q x y) y := by
  have hA' : HasDerivAt (fun t => fairAverage x t) (1 / 2) y := by
    simpa [fairAverage] using ((hasDerivAt_id y).const_add (x + 2)).div_const 2
  have hN : HasDerivAt (fun t => fairNumerator q x t) (-x + q / 2 * (x - y)) y := by
    have h := ((hasDerivAt_const y (1 : ℝ)).sub ((hasDerivAt_id y).const_mul x)).sub
      ((((hasDerivAt_id y).const_sub x).pow 2).const_mul (q / 4))
    convert h using 1
    · ext t
      simp [fairNumerator]
    · simp only [id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one,
        zero_sub]
      ring
  have hNx : HasDerivAt (fun t : ℝ => -t - q / 2 * (x - t)) (-1 + q / 2) y := by
    convert ((hasDerivAt_id y).neg).sub (((hasDerivAt_id y).const_sub x).const_mul (q / 2)) using 1
    · ext t
      simp
    · ring
  have h := (hA'.rpow_const (p := q - 3) (Or.inl hA.ne')).mul
    ((hNx.mul hA').add (hN.const_mul ((q - 2) / 2)))
  convert h using 1
  · rfl
  · simp only [Pi.mul_apply, Pi.add_apply, show q - 3 - 1 = q - 4 by ring]
    have hpow : fairAverage x y ^ (q - 3) = fairAverage x y ^ (q - 4) * fairAverage x y := by
      rw [← Real.rpow_add_one hA.ne']
      congr 1
      ring
    rw [hpow]
    unfold fairKernelMixedDerivative fairNumerator fairAverage
    ring

/-- Strict positivity of the mixed partial throughout the sub-hyperbola region. -/
theorem fairKernelMixedDerivative_pos (q x y : ℝ) (hq₀ : 0 < q) (hq₁ : q < 1)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x * y < 1) :
    0 < fairKernelMixedDerivative q x y := by
  have hA : 0 < fairAverage x y := by unfold fairAverage; positivity
  have hqq : 0 < (q - 2) * (q - 1) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
  have hb : (q - 2) * (x - y) ^ 2 + 4 * x * y - 4 < 0 := by
    have hs := mul_nonpos_of_nonpos_of_nonneg (by linarith : q - 2 ≤ 0) (sq_nonneg (x - y))
    nlinarith
  unfold fairKernelMixedDerivative
  exact mul_pos_of_neg_of_neg
    (mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (neg_neg_of_pos hqq) (by norm_num))
      (Real.rpow_pos_of_pos hA _)) hb

/-- The finite rational identity behind the boundary normal square. -/
theorem fair_boundary_square_algebra (q x U : ℝ) (hx : x ≠ 0) (hU : U ≠ 1) (hx₁ : x + 1 ≠ 0) :
    (2 * (-q * x ^ 2 + q - 2) - q * (q - 2) * (x - 1) ^ 2) / (x + 1) +
      q * U * (x - 1) *
        (x * (2 * (x + 1) + (x - 1) * (2 * q - 2)) * (U - 1) -
          (x ^ 2 - 1) * q * U) / (x ^ 2 * (U - 1) ^ 2) =
      -(U * q * x - U * q - 2 * U * x + q * x ^ 2 - q * x + 2 * x) ^ 2 /
        (x ^ 2 * (U - 1) ^ 2 * (x + 1)) := by
  have hUm : U - 1 ≠ 0 := sub_ne_zero.mpr hU
  field_simp
  ring

end RenyiMonotonicity
