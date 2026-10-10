module

public import RenyiMonotonicity.Definitions

@[expose] public section

open scoped Topology
open Set

namespace RenyiMonotonicity

/-- The even-power numerator after the change of variables `t = δ/(1-δ)`. -/
def harmonicDifference (p : ℕ) (y t : ℝ) : ℝ := (t + y) ^ p - (t - y) ^ p

def harmonicDifferenceDerivative (p : ℕ) (y t : ℝ) : ℝ :=
  (p : ℝ) * ((t + y) ^ (p - 1) - (t - y) ^ (p - 1))

/-- The gap-dependent part of the lowering kernel after the rational substitution. -/
noncomputable def harmonicTransformedKernel (p : ℕ) (q y t : ℝ) : ℝ :=
  harmonicDifference p y t * (1 + t) ^ (q - p)

theorem hasDerivAt_harmonicDifference (p : ℕ) (y t : ℝ) :
    HasDerivAt (harmonicDifference p y) (harmonicDifferenceDerivative p y t) t := by
  have h := (((hasDerivAt_id t).add_const y).pow p).sub
    (((hasDerivAt_id t).sub_const y).pow p)
  convert h using 1
  · ext u
    simp [harmonicDifference]
  · simp [harmonicDifferenceDerivative]
    ring

/-- A convex tangent inequality for every nonzero even power on the whole real line. -/
theorem harmonic_even_tangent (p : ℕ) (hp : Even p) (a b : ℝ) (hba : b < a) :
    (p : ℝ) * b ^ (p - 1) * (a - b) ≤ a ^ p - b ^ p := by
  have h := (hp.convexOn_pow (𝕜 := ℝ)).le_slope_of_hasDerivAt
    (mem_univ b) (mem_univ a) hba (hasDerivAt_pow p b)
  rw [slope_def_field] at h
  exact (le_div_iff₀ (sub_pos.mpr hba)).mp h

theorem harmonicDifference_pos (p : ℕ) (hp : Even p) (hp0 : 0 < p)
    (y t : ℝ) (hy : 0 < y) (ht : 0 < t) : 0 < harmonicDifference p y t := by
  have habs : |t - y| < t + y := abs_lt.mpr ⟨by linarith, by linarith⟩
  have hpow := pow_lt_pow_left₀ habs (abs_nonneg (t - y)) (Nat.ne_of_gt hp0)
  rw [hp.pow_abs] at hpow
  exact sub_pos.mpr hpow

theorem harmonicDifferenceDerivative_pos (p : ℕ) (hp : Even p) (hp0 : 0 < p)
    (y t : ℝ) (hy : 0 < y) : 0 < harmonicDifferenceDerivative p y t := by
  have hodd : Odd (p - 1) := Nat.Even.sub_odd hp0 hp (by decide : Odd 1)
  exact mul_pos (Nat.cast_pos.mpr hp0)
    (sub_pos.mpr (hodd.strictMono_pow (by linarith : t - y < t + y)))

/-- Exact logarithmic-derivative lower bound, expressed without division. -/
theorem harmonicDifference_derivative_lower (p : ℕ) (hp : Even p) (hp0 : 0 < p)
    (y t : ℝ) (hy : 0 < y) :
    ((p : ℝ) - 1) * harmonicDifference p y t ≤
      (t + y) * harmonicDifferenceDerivative p y t := by
  have htangent := harmonic_even_tangent p hp (t + y) (t - y) (by linarith)
  have hpower (a : ℝ) : a ^ p = a * a ^ (p - 1) := by
    nth_rw 1 [← Nat.sub_add_cancel hp0]
    rw [pow_succ']
  dsimp [harmonicDifference, harmonicDifferenceDerivative]
  rw [hpower (t + y), hpower (t - y)] at htangent ⊢
  nlinarith

/-- The derivative numerator is nonnegative simultaneously for every `q ≥ 1`. -/
theorem harmonicTransformedKernel_derivative_bracket_nonneg
    (p : ℕ) (hp : Even p) (hp0 : 0 < p) (q y t : ℝ)
    (hq : 1 ≤ q) (hy : 0 < y) (hy1 : y ≤ 1) (ht : 0 < t) :
    0 ≤ (1 + t) * harmonicDifferenceDerivative p y t +
      (q - p) * harmonicDifference p y t := by
  have hlow := harmonicDifference_derivative_lower p hp hp0 y t hy
  have hD := harmonicDifference_pos p hp hp0 y t hy ht
  have hD' := harmonicDifferenceDerivative_pos p hp hp0 y t hy
  have hterm1 : 0 ≤ (1 - y) * harmonicDifferenceDerivative p y t :=
    mul_nonneg (sub_nonneg.mpr hy1) hD'.le
  have hterm2 : 0 ≤ (q - 1) * harmonicDifference p y t :=
    mul_nonneg (sub_nonneg.mpr hq) hD.le
  nlinarith

/-- Exact derivative of the transformed lowering kernel on its positive domain. -/
theorem hasDerivAt_harmonicTransformedKernel (p : ℕ) (q y t : ℝ) (ht : 0 < t) :
    HasDerivAt (harmonicTransformedKernel p q y)
      ((1 + t) ^ (q - p - 1) *
        ((1 + t) * harmonicDifferenceDerivative p y t +
          (q - p) * harmonicDifference p y t)) t := by
  have hbase : 0 < 1 + t := by linarith
  have h := (hasDerivAt_harmonicDifference p y t).mul
    (((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).rpow_const
      (p := q - p) (Or.inl (ne_of_gt hbase)))
  convert h using 1
  · ext u
    simp [harmonicTransformedKernel]
  · have hpow : (1 + t) ^ (q - p) = (1 + t) ^ (q - p - 1) * (1 + t) := by
      calc
        (1 + t) ^ (q - p) = (1 + t) ^ ((q - p - 1) + 1) := by congr 1; ring
        _ = (1 + t) ^ (q - p - 1) * (1 + t) := by
          rw [Real.rpow_add hbase, Real.rpow_one]
    simp only [Pi.add_apply, id_eq, zero_add]
    rw [hpow]
    ring

/-- Pointwise gap monotonicity after `t=δ/(1-δ)`, for all orders `q ≥ 1`.
No power-series coefficient monotonicity is assumed. -/
theorem harmonicTransformedKernel_monotoneOn (p : ℕ) (hp : Even p) (hp0 : 0 < p)
    (q y : ℝ) (hq : 1 ≤ q) (hy : 0 < y) (hy1 : y ≤ 1) :
    MonotoneOn (harmonicTransformedKernel p q y) (Ioi 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
    (f' := fun t => (1 + t) ^ (q - p - 1) *
      ((1 + t) * harmonicDifferenceDerivative p y t +
        (q - p) * harmonicDifference p y t))
  · intro t ht
    exact (hasDerivAt_harmonicTransformedKernel p q y t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hasDerivAt_harmonicTransformedKernel p q y t (by simpa using ht)).hasDerivWithinAt
  · intro t ht
    have ht' : 0 < t := by simpa using ht
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (harmonicTransformedKernel_derivative_bracket_nonneg p hp hp0 q y t hq hy hy1 ht')

/-- Odd power difference in the entropy order. -/
noncomputable def harmonicOddDenominator (q x : ℝ) : ℝ :=
  (1 / 2 + x) ^ q - (1 / 2 - x) ^ q

/-- The original lowering quotient away from its removable center. -/
noncomputable def harmonicLoweringQuotient (p : ℕ) (q δ x : ℝ) : ℝ :=
  (((1 - δ) * x + δ / 2) ^ p - ((1 - δ) * x - δ / 2) ^ p) /
    ((1 - δ) ^ q * harmonicOddDenominator q x)

theorem harmonicOddDenominator_pos (q x : ℝ) (hq : 0 < q) (hx : 0 < x)
    (hx1 : x ≤ 1 / 2) : 0 < harmonicOddDenominator q x := by
  apply sub_pos.mpr
  exact Real.rpow_lt_rpow (by linarith) (by linarith) hq

/-- Exact rational change of variables used by harmonic lowering. -/
theorem harmonicLoweringQuotient_eq_transformed (p : ℕ) (hp : Even p) (q δ x : ℝ)
    (_hδ : 0 < δ) (hδ1 : δ < 1) :
    harmonicLoweringQuotient p q δ x =
      harmonicTransformedKernel p q (2 * x) (δ / (1 - δ)) /
        ((2 : ℝ) ^ p * harmonicOddDenominator q x) := by
  have hd : 0 < 1 - δ := sub_pos.mpr hδ1
  have hd0 := ne_of_gt hd
  have hplus : (1 - δ) * x + δ / 2 =
      ((1 - δ) / 2) * (δ / (1 - δ) + 2 * x) := by field_simp; ring
  have hminus : (1 - δ) * x - δ / 2 =
      -((1 - δ) / 2) * (δ / (1 - δ) - 2 * x) := by field_simp; ring
  have hone : 1 + δ / (1 - δ) = (1 - δ)⁻¹ := by field_simp; ring
  have hrpow : (1 + δ / (1 - δ)) ^ (q - p) = (1 - δ) ^ p / (1 - δ) ^ q := by
    rw [hone, ← Real.rpow_neg_eq_inv_rpow,
      show -(q - (p : ℝ)) = (p : ℝ) - q by ring,
      Real.rpow_sub hd, Real.rpow_natCast]
  unfold harmonicLoweringQuotient harmonicTransformedKernel harmonicDifference
  rw [hplus, hminus, mul_pow, mul_pow, hp.neg_pow, div_pow, hrpow]
  ring

/-- The rational substitution is strictly increasing on the full admissible gap interval. -/
theorem harmonic_gap_substitution_strictMonoOn :
    StrictMonoOn (fun δ : ℝ => δ / (1 - δ)) (Ioo 0 1) := by
  intro a ha b hb hab
  rw [div_lt_div_iff₀ (sub_pos.mpr ha.2) (sub_pos.mpr hb.2)]
  nlinarith

/-- The original lowering quotient increases pointwise with the gap at positive spatial points. -/
theorem harmonicLoweringQuotient_monotoneOn_positive (p : ℕ) (hp : Even p) (hp0 : 0 < p)
    (q x : ℝ) (hq : 1 ≤ q) (hx : 0 < x) (hx1 : x ≤ 1 / 2) :
    MonotoneOn (fun δ : ℝ => harmonicLoweringQuotient p q δ x) (Ioo 0 1) := by
  intro a ha b hb hab
  change harmonicLoweringQuotient p q a x ≤ harmonicLoweringQuotient p q b x
  rw [harmonicLoweringQuotient_eq_transformed p hp q a x ha.1 ha.2,
    harmonicLoweringQuotient_eq_transformed p hp q b x hb.1 hb.2]
  apply div_le_div_of_nonneg_right _
    (mul_nonneg (by positivity) (harmonicOddDenominator_pos q x (by linarith) hx hx1).le)
  apply harmonicTransformedKernel_monotoneOn p hp hp0 q (2 * x) hq
    (by linarith) (by linarith)
  · exact div_pos ha.1 (sub_pos.mpr ha.2)
  · exact div_pos hb.1 (sub_pos.mpr hb.2)
  · exact harmonic_gap_substitution_strictMonoOn.monotoneOn ha hb hab

/-- The lowering quotient is even in its spatial argument. -/
theorem harmonicLoweringQuotient_neg (p : ℕ) (hp : Even p) (q δ x : ℝ) :
    harmonicLoweringQuotient p q δ (-x) = harmonicLoweringQuotient p q δ x := by
  have hplus : (1 - δ) * -x + δ / 2 = -((1 - δ) * x - δ / 2) := by ring
  have hminus : (1 - δ) * -x - δ / 2 = -((1 - δ) * x + δ / 2) := by ring
  unfold harmonicLoweringQuotient harmonicOddDenominator
  rw [hplus, hminus, hp.neg_pow, hp.neg_pow]
  simp only [← sub_eq_add_neg, sub_neg_eq_add]
  rw [show (((1 - δ) * x - δ / 2) ^ p - ((1 - δ) * x + δ / 2) ^ p) =
    -(((1 - δ) * x + δ / 2) ^ p - ((1 - δ) * x - δ / 2) ^ p) by ring]
  rw [show (1 / 2 - x) ^ q - (1 / 2 + x) ^ q =
    -((1 / 2 + x) ^ q - (1 / 2 - x) ^ q) by ring, mul_neg, neg_div_neg_eq]

/-- Removable central value, stated in the derivative-ratio form used to verify the limit. -/
noncomputable def harmonicCenterValue (p : ℕ) (q δ : ℝ) : ℝ :=
  ((2 : ℝ) * p * (1 - δ) * (δ / 2) ^ (p - 1)) /
    (2 * (1 - δ) ^ q * q * (1 / 2 : ℝ) ^ (q - 1))

/-- The lowering kernel with its explicitly filled removable center. -/
noncomputable def harmonicLoweringKernel (p : ℕ) (q δ x : ℝ) : ℝ :=
  if x = 0 then harmonicCenterValue p q δ else harmonicLoweringQuotient p q δ x

/-- Quotient limit from two derivatives with simultaneous simple zeros. -/
theorem harmonic_tendsto_quotient_zero {f g : ℝ → ℝ} {a b : ℝ}
    (hf : HasDerivAt f a 0) (hg : HasDerivAt g b 0)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hb : b ≠ 0) :
    Filter.Tendsto (fun x => f x / g x) (𝓝[≠] 0) (𝓝 (a / b)) := by
  apply (hf.tendsto_slope.div hg.tendsto_slope hb).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [mem_compl_iff, mem_singleton_iff] at hx
  change slope f 0 x / slope g 0 x = f x / g x
  rw [slope_def_field, slope_def_field, hf0, hg0, sub_zero, sub_zero, sub_zero,
    div_div_div_cancel_right₀ hx]

/-- The center value is the true limit of the original quotient; no endpoint series is assumed. -/
theorem harmonicLoweringQuotient_tendsto_zero (p : ℕ) (hp : Even p) (hp0 : 0 < p)
    (q δ : ℝ) (hq : 0 < q) (hδ1 : δ < 1) :
    Filter.Tendsto (harmonicLoweringQuotient p q δ) (𝓝[≠] 0)
      (𝓝 (harmonicCenterValue p q δ)) := by
  have hodd : Odd (p - 1) := Nat.Even.sub_odd hp0 hp (by decide : Odd 1)
  have hnum : HasDerivAt
      (fun x : ℝ => ((1 - δ) * x + δ / 2) ^ p - ((1 - δ) * x - δ / 2) ^ p)
      (2 * p * (1 - δ) * (δ / 2) ^ (p - 1)) 0 := by
    have h := ((((hasDerivAt_id (0 : ℝ)).const_mul (1 - δ)).add_const (δ / 2)).pow p).sub
      ((((hasDerivAt_id (0 : ℝ)).const_mul (1 - δ)).sub_const (δ / 2)).pow p)
    convert h using 1
    · ext x
      simp
    · simp only [id_eq, mul_zero, zero_add, zero_sub, hodd.neg_pow, mul_one]
      ring
  have hden : HasDerivAt (fun x : ℝ => (1 - δ) ^ q * harmonicOddDenominator q x)
      (2 * (1 - δ) ^ q * q * (1 / 2 : ℝ) ^ (q - 1)) 0 := by
    have hplus := ((hasDerivAt_const (0 : ℝ) (1 / 2 : ℝ)).add (hasDerivAt_id 0)).rpow_const
      (p := q) (Or.inl (by norm_num))
    have hminus := ((hasDerivAt_const (0 : ℝ) (1 / 2 : ℝ)).sub (hasDerivAt_id 0)).rpow_const
      (p := q) (Or.inl (by norm_num))
    have h := (hplus.sub hminus).const_mul ((1 - δ) ^ q)
    convert h using 1
    · ext x
      simp [harmonicOddDenominator]
    · simp only [Pi.add_apply, Pi.sub_apply, id_eq, zero_add, zero_sub, add_zero, sub_zero]
      ring
  have hdenpos : 0 < 2 * (1 - δ) ^ q * q * (1 / 2 : ℝ) ^ (q - 1) := by
    apply mul_pos
    · exact mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (sub_pos.mpr hδ1) q)) hq
    · exact Real.rpow_pos_of_pos (by norm_num) _
  apply harmonic_tendsto_quotient_zero hnum hden _ _ (ne_of_gt hdenpos)
  · simp [hp.neg_pow]
  · simp [harmonicOddDenominator]

/-- The completed kernel is continuous at its center. -/
theorem continuousAt_harmonicLoweringKernel_zero (p : ℕ) (hp : Even p) (hp0 : 0 < p)
    (q δ : ℝ) (hq : 0 < q) (hδ1 : δ < 1) :
    ContinuousAt (harmonicLoweringKernel p q δ) 0 := by
  rw [continuousAt_iff_punctured_nhds]
  simp only [harmonicLoweringKernel, ↓reduceIte]
  apply (harmonicLoweringQuotient_tendsto_zero p hp hp0 q δ hq hδ1).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [mem_compl_iff, mem_singleton_iff] at hx
  simp [harmonicLoweringKernel, hx]

theorem harmonicLoweringKernel_neg (p : ℕ) (hp : Even p) (q δ x : ℝ) :
    harmonicLoweringKernel p q δ (-x) = harmonicLoweringKernel p q δ x := by
  simp only [harmonicLoweringKernel, neg_eq_zero, harmonicLoweringQuotient_neg p hp]

/-- Center monotonicity follows from the verified removable limit and off-center inequalities. -/
theorem harmonicLoweringKernel_zero_monotoneOn (p : ℕ) (hp : Even p) (hp0 : 0 < p)
    (q : ℝ) (hq : 1 ≤ q) :
    MonotoneOn (fun δ : ℝ => harmonicLoweringKernel p q δ 0) (Ioo 0 1) := by
  intro a ha b hb hab
  have hlimA := (continuousAt_harmonicLoweringKernel_zero p hp hp0 q a
    (by linarith) ha.2).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hlimB := (continuousAt_harmonicLoweringKernel_zero p hp hp0 q b
    (by linarith) hb.2).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  apply le_of_tendsto_of_tendsto hlimA hlimB
  have hsmall : ∀ᶠ x : ℝ in 𝓝[>] 0, x < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with x hx hx1
  have hx0 : x ≠ 0 := ne_of_gt hx
  simp only [harmonicLoweringKernel, hx0, ↓reduceIte]
  exact harmonicLoweringQuotient_monotoneOn_positive p hp hp0 q x hq hx hx1.le ha hb hab

/-- Full pointwise gap monotonicity on the closed spatial interval, including both
outer points and the rigorously filled center. -/
theorem harmonicLoweringKernel_monotoneOn (p : ℕ) (hp : Even p) (hp0 : 0 < p)
    (q x : ℝ) (hq : 1 ≤ q) (hx : |x| ≤ 1 / 2) :
    MonotoneOn (fun δ : ℝ => harmonicLoweringKernel p q δ x) (Ioo 0 1) := by
  by_cases hx0 : x = 0
  · subst x
    exact harmonicLoweringKernel_zero_monotoneOn p hp hp0 q hq
  · rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · intro a ha b hb hab
      have hpneg : 0 < -x := neg_pos.mpr hneg
      have hpneg1 : -x ≤ 1 / 2 := by simpa [abs_of_neg hneg] using hx
      have h := harmonicLoweringQuotient_monotoneOn_positive p hp hp0 q (-x)
        hq hpneg hpneg1 ha hb hab
      simpa [harmonicLoweringKernel, hx0, harmonicLoweringQuotient_neg p hp] using h
    · intro a ha b hb hab
      simpa [harmonicLoweringKernel, hx0] using
        harmonicLoweringQuotient_monotoneOn_positive p hp hp0 q x hq hpos
          (by simpa [abs_of_pos hpos] using hx) ha hb hab

end RenyiMonotonicity
