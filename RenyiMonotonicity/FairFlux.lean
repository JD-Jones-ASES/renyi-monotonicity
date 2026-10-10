module

public import RenyiMonotonicity.FairLocal

@[expose] public section

namespace RenyiMonotonicity

/-- Homogeneous correction flux, with its exact one-sided zero-edge values. -/
noncomputable def fairFlux (q a b : ℝ) : ℝ :=
  if b = 0 then q * (2 : ℝ) ^ (-q) * a ^ q else b ^ q * fairCorrection q (a / b)

@[simp] theorem fairFlux_right_zero (q a : ℝ) :
    fairFlux q a 0 = q * (2 : ℝ) ^ (-q) * a ^ q := by simp [fairFlux]

theorem fairFlux_left_zero (q b : ℝ) (hq : 0 < q) :
    fairFlux q 0 b = -q * (2 : ℝ) ^ (-q) * b ^ q := by
  by_cases hb : b = 0
  · simp [hb, fairFlux, Real.zero_rpow hq.ne']
  · simp only [fairFlux, ite_eq_right hb, zero_div, fairCorrection_zero q hq.ne']
    ring

/-- Antisymmetry holds on the entire closed nonnegative quadrant. -/
theorem fairFlux_antisymm (q a b : ℝ) (hq : 0 < q) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    fairFlux q a b = -fairFlux q b a := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · rw [fairFlux_left_zero q b hq, fairFlux_right_zero]
    ring
  rcases eq_or_lt_of_le hb with rfl | hb
  · rw [fairFlux_right_zero, fairFlux_left_zero q a hq]
    ring
  have hr := fairCorrection_reciprocal q (a / b) hq.ne' (div_pos ha hb)
  rw [inv_div] at hr
  rw [Real.div_rpow ha.le hb.le] at hr
  have hbq : b ^ q ≠ 0 := (Real.rpow_pos_of_pos hb q).ne'
  unfold fairFlux
  rw [ite_eq_right hb.ne', ite_eq_right ha.ne']
  have hh := congrArg (fun t : ℝ => b ^ q * t) hr
  field_simp at hh
  nlinarith

/-- The uncorrected local derivative term. -/
noncomputable def fairLocalTerm (q a b c : ℝ) : ℝ :=
  (b ^ 2 - a * c - q * ((c - a) / 2) ^ 2) * ((a + 2 * b + c) / 2) ^ (q - 2)

theorem fairLocalTerm_symm (q a b c : ℝ) :
    fairLocalTerm q a b c = fairLocalTerm q c b a := by
  unfold fairLocalTerm
  rw [show c + 2 * b + a = a + 2 * b + c by ring,
    show ((a - c) / 2) ^ 2 = ((c - a) / 2) ^ 2 by ring]
  ring

/-- Exact positive homogeneity, with no division by a vanishing outer mass. -/
theorem fairLocalTerm_normalize (q a b c : ℝ) (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c) :
    fairLocalTerm q a b c = b ^ q * fairKernel q (a / b) (c / b) := by
  have hA : 0 ≤ fairAverage (a / b) (c / b) := by
    unfold fairAverage
    positivity
  have hav : (a + 2 * b + c) / 2 = b * fairAverage (a / b) (c / b) := by
    unfold fairAverage
    field_simp
  have hnum : b ^ 2 - a * c - q * ((c - a) / 2) ^ 2 =
      b ^ 2 * fairNumerator q (a / b) (c / b) := by
    unfold fairNumerator
    field_simp
    ring
  unfold fairLocalTerm fairKernel
  rw [hav, hnum, Real.mul_rpow hb.le hA, Real.rpow_sub hb, Real.rpow_two]
  field_simp

/-- Local correction equals the normalized strictly positive scalar term. -/
theorem fairLocalTerm_add_flux (q a b c : ℝ) (hq : 0 < q)
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c) :
    fairLocalTerm q a b c + fairFlux q a b - fairFlux q b c =
      b ^ q * fairCorrectedKernel q (a / b) (c / b) := by
  rw [fairLocalTerm_normalize q a b c ha hb hc, fairFlux_antisymm q b c hq hb.le hc]
  simp only [fairFlux, ite_eq_right hb.ne', fairCorrectedKernel]
  ring

/-- Strict corrected inequality whenever the middle entry is positive and its
log-concavity inequality is strict. -/
theorem fairLocalTerm_add_flux_pos (q a b c : ℝ) (hq₀ : 0 < q) (hq₁ : q < 1)
    (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 ≤ c) (hlc : a * c < b ^ 2) :
    0 < fairLocalTerm q a b c + fairFlux q a b - fairFlux q b c := by
  rw [fairLocalTerm_add_flux q a b c hq₀ ha hb hc]
  apply mul_pos (Real.rpow_pos_of_pos hb q)
  apply fairCorrectedKernel_pos q (a / b) (c / b) hq₀ hq₁ (div_nonneg ha hb.le) (div_nonneg hc hb.le)
  rw [div_mul_div_comm, div_lt_one (mul_pos hb hb)]
  nlinarith

/-- Exact boundary value for a triple with only its right entry nonzero. -/
theorem fairLocalTerm_zero_zero (q c : ℝ) (hq : 0 < q) (hc : 0 ≤ c) :
    fairLocalTerm q 0 0 c = -q * (2 : ℝ) ^ (-q) * c ^ q := by
  rcases eq_or_lt_of_le hc with rfl | hc
  · simp [fairLocalTerm, Real.zero_rpow hq.ne']
  have hp : 0 < c / 2 := div_pos hc (by norm_num)
  unfold fairLocalTerm
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul, mul_zero, sub_zero, zero_add, zero_sub, neg_mul]
  rw [Real.rpow_sub hp, Real.rpow_two]
  have he : -q * (c / 2) ^ 2 * ((c / 2) ^ q / (c / 2) ^ 2) = -q * (c / 2) ^ q := by
    field_simp
  simp only [← neg_mul] at ⊢
  rw [he, Real.div_rpow hc.le (by norm_num), Real.rpow_neg (by norm_num)]
  ring

/-- Nonstrict corrected inequality includes the zero-middle support edges. -/
theorem fairLocalTerm_add_flux_nonneg (q a b c : ℝ) (hq₀ : 0 < q) (hq₁ : q < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hlc : a * c ≤ b ^ 2) :
    0 ≤ fairLocalTerm q a b c + fairFlux q a b - fairFlux q b c := by
  rcases eq_or_lt_of_le hb with rfl | hb
  · have he : a * c = 0 := le_antisymm (by simpa using hlc) (mul_nonneg ha hc)
    rcases mul_eq_zero.mp he with rfl | rfl
    · rw [fairLocalTerm_zero_zero q c hq₀ hc, fairFlux_left_zero q 0 hq₀,
        fairFlux_left_zero q c hq₀, Real.zero_rpow hq₀.ne']
      ring_nf
      exact le_refl _
    · rw [fairLocalTerm_symm, fairLocalTerm_zero_zero q a hq₀ ha, fairFlux_right_zero,
        fairFlux_right_zero, Real.zero_rpow hq₀.ne']
      ring_nf
      exact le_refl _
  · rw [fairLocalTerm_add_flux q a b c hq₀ ha hb hc]
    apply mul_nonneg (Real.rpow_nonneg hb.le q)
    apply fairCorrectedKernel_nonneg q (a / b) (c / b) hq₀ hq₁ (div_nonneg ha hb.le) (div_nonneg hc hb.le)
    rw [div_mul_div_comm, div_le_one (mul_pos hb hb)]
    nlinarith

end RenyiMonotonicity
