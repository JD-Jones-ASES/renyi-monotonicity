module

public import RenyiMonotonicity.Definitions

@[expose] public section

open scoped Topology
open Filter Set

namespace RenyiMonotonicity

/-- Scalar correction used to make the fair-coordinate derivative telescope.
The field convention already gives its removable value zero at one. -/
noncomputable def fairCorrection (q x : ℝ) : ℝ :=
  q * (2 : ℝ) ^ (-q) * (x - 1) ^ 2 * (x + 1) ^ (2 * q - 2) / (x ^ q - 1)

@[simp] theorem fairCorrection_one (q : ℝ) : fairCorrection q 1 = 0 := by
  simp [fairCorrection]

@[simp] theorem fairCorrection_zero (q : ℝ) (hq : q ≠ 0) :
    fairCorrection q 0 = -q * (2 : ℝ) ^ (-q) := by
  simp [fairCorrection, Real.zero_rpow hq]
  ring

/-- A normalized expression for the derivative away from the removable point. -/
noncomputable def fairCorrectionRegularDerivative (q x : ℝ) : ℝ :=
  q * (2 : ℝ) ^ (-q) * (x - 1) * (x + 1) ^ (2 * q - 3) *
    ((2 * (x + 1) + (x - 1) * (2 * q - 2)) * (x ^ q - 1) -
      (x - 1) * (x + 1) * q * x ^ (q - 1)) / (x ^ q - 1) ^ 2

/-- Actual differentiability of the correction at every positive point other than one. -/
theorem hasDerivAt_fairCorrection_regular (q x : ℝ) (hq : q ≠ 0)
    (hx : 0 < x) (hx₁ : x ≠ 1) :
    HasDerivAt (fairCorrection q) (fairCorrectionRegularDerivative q x) x := by
  have hp : 0 < x + 1 := by linarith
  have hd : x ^ q - 1 ≠ 0 := by
    intro he
    have hh : x ^ q = (1 : ℝ) ^ q := by simpa using sub_eq_zero.mp he
    exact hx₁ ((Real.rpow_left_inj hx.le zero_le_one hq).mp hh)
  have hpow : (x + 1) ^ (2 * q - 2) = (x + 1) ^ (2 * q - 3) * (x + 1) := by
    rw [← Real.rpow_add_one hp.ne']
    congr 1
    ring
  have h := (((((hasDerivAt_id x).sub_const 1).pow 2).const_mul
    (q * (2 : ℝ) ^ (-q))).mul
    (((hasDerivAt_id x).add_const 1).rpow_const (p := 2 * q - 2) (Or.inl hp.ne'))).div
    (((hasDerivAt_id x).rpow_const (p := q) (Or.inl hx.ne')).sub_const 1) hd
  convert h using 1
  · ext t
    simp [fairCorrection]
  · simp only [fairCorrectionRegularDerivative, Nat.cast_ofNat, Nat.add_one_sub_one,
      pow_one, mul_one, one_mul, id_eq, Pi.pow_apply, Pi.mul_apply,
      show 2 * q - 2 - 1 = 2 * q - 3 by ring]
    rw [hpow]
    congr 1
    ring

/-- The derivative at the removable point follows from the ordinary derivative
of `x ↦ x^q`, not from a postulated smooth extension. -/
theorem hasDerivAt_fairCorrection_one (q : ℝ) (hq : q ≠ 0) :
    HasDerivAt (fairCorrection q) ((2 : ℝ) ^ (q - 2)) 1 := by
  have hr : HasDerivAt (fun x : ℝ => x ^ q) q 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).rpow_const (p := q) (Or.inl one_ne_zero)
  have hp : Tendsto (fun x : ℝ => q * (2 : ℝ) ^ (-q) * (x + 1) ^ (2 * q - 2))
      (𝓝[≠] 1) (𝓝 (q * (2 : ℝ) ^ (-q) * (2 : ℝ) ^ (2 * q - 2))) := by
    have hc : ContinuousAt (fun x : ℝ => q * (2 : ℝ) ^ (-q) * (x + 1) ^ (2 * q - 2)) 1 := by
      exact continuousAt_const.mul
        ((Real.continuousAt_rpow_const (1 + 1) (2 * q - 2) (Or.inl (by norm_num))).comp (f := fun t : ℝ => t + 1)
          (continuousAt_id.add_const 1))
    simpa only [one_add_one_eq_two] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hquot := hp.div hr.tendsto_slope hq
  have he : (q * (2 : ℝ) ^ (-q) * (2 : ℝ) ^ (2 * q - 2)) / q =
      (2 : ℝ) ^ (q - 2) := by
    rw [mul_assoc, ← Real.rpow_add (by norm_num)]
    rw [show -q + (2 * q - 2) = q - 2 by ring]
    field_simp
  rw [he] at hquot
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply hquot.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx₁ : x ≠ 1 := by simpa using hx
  simp only [Pi.div_apply, slope_def_field, fairCorrection_one, Real.one_rpow, sub_zero]
  unfold fairCorrection
  field_simp

/-- The first derivative of the correction, with its independently established center. -/
noncomputable def fairCorrectionDerivative (q x : ℝ) : ℝ :=
  if x = 1 then (2 : ℝ) ^ (q - 2) else fairCorrectionRegularDerivative q x

theorem hasDerivAt_fairCorrection (q x : ℝ) (hq : q ≠ 0) (hx : 0 < x) :
    HasDerivAt (fairCorrection q) (fairCorrectionDerivative q x) x := by
  by_cases hx₁ : x = 1
  · subst x
    simpa [fairCorrectionDerivative] using hasDerivAt_fairCorrection_one q hq
  · simpa [fairCorrectionDerivative, hx₁] using hasDerivAt_fairCorrection_regular q x hq hx hx₁

/-- Continuity at every nonnegative scalar, including zero and the removable point. -/
theorem continuousOn_fairCorrection (q : ℝ) (hq : 0 < q) :
    ContinuousOn (fairCorrection q) (Ici 0) := by
  intro x hx
  by_cases hx₁ : x = 1
  · subst x
    exact (hasDerivAt_fairCorrection_one q (ne_of_gt hq)).continuousAt.continuousWithinAt
  have hp : 0 < x + 1 := by change 0 ≤ x at hx; linarith
  have hd : x ^ q - 1 ≠ 0 := by
    intro he
    have hh : x ^ q = (1 : ℝ) ^ q := by simpa using sub_eq_zero.mp he
    exact hx₁ ((Real.rpow_left_inj hx zero_le_one (ne_of_gt hq)).mp hh)
  apply ContinuousAt.continuousWithinAt
  unfold fairCorrection
  apply ContinuousAt.div
  · exact (continuousAt_const.mul ((continuousAt_id.sub_const 1).pow 2)).mul
      ((Real.continuousAt_rpow_const (x + 1) (2 * q - 2) (Or.inl hp.ne')).comp (f := fun t : ℝ => t + 1)
        (continuousAt_id.add_const 1))
  · exact ((Real.continuous_rpow_const hq.le).continuousAt).sub continuousAt_const
  · exact hd

/-- Exact reciprocal antisymmetry of the homogeneous scalar correction. -/
theorem fairCorrection_reciprocal (q x : ℝ) (hq : q ≠ 0) (hx : 0 < x) :
    x ^ q * fairCorrection q x⁻¹ = -fairCorrection q x := by
  by_cases hx₁ : x = 1
  · subst x
    simp
  have hU : x ^ q ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hx q)
  have hUm : x ^ q - 1 ≠ 0 := by
    intro h
    exact hx₁ ((Real.rpow_left_inj hx.le zero_le_one hq).mp (by simpa using sub_eq_zero.mp h))
  have hplus : x⁻¹ + 1 = (x + 1) / x := by field_simp; ring
  have hpow : x ^ (2 * q - 2) = (x ^ q) ^ 2 / x ^ 2 := by
    rw [show 2 * q - 2 = q * 2 - (2 : ℕ) by push_cast; ring,
      Real.rpow_sub_natCast hx.ne', Real.rpow_mul hx.le, Real.rpow_two]
  have h1U : 1 - x ^ q ≠ 0 := by intro h; apply hUm; linarith
  unfold fairCorrection
  rw [hplus, Real.div_rpow (by linarith : 0 ≤ x + 1) hx.le,
    Real.inv_rpow hx.le, hpow]
  field_simp [h1U]
  ring

end RenyiMonotonicity
