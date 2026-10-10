module

public import RenyiMonotonicity.PositiveSeries
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Complex.AbelLimit
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

open scoped BigOperators Topology
open Filter Set

namespace RenyiMonotonicity

/-- The positive even factor in harmonic lowering, with its removable center filled in. -/
noncomputable def harmonicEvenKernel (q x : ℝ) : ℝ :=
  if x = 0 then (2 : ℝ) ^ (q - 1) / q else 2 * x / ((1 / 2 + x) ^ q - (1 / 2 - x) ^ q)

/-- The negative odd binomial tail, indexed by its strictly positive even degree. -/
noncomputable def harmonicBinomialCoefficient (q : ℝ) (n : ℕ) : ℝ :=
  -Ring.choose q (2 * n + 3) / q

/-- The falling-factorial recurrence, in a division-free real form. -/
theorem real_choose_mul_succ (q : ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * Ring.choose q (n + 1) = (q - n) * Ring.choose q n := by
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul,
    descPochhammer_succ_right]
  simp only [Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
    Polynomial.smeval_natCast, smul_eq_mul, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The binomial expansion on its open convergence interval, as an ordinary real series. -/
theorem hasSum_real_binomial (q y : ℝ) (hy : |y| < 1) :
    HasSum (fun n : ℕ => Ring.choose q n * y ^ n) ((1 + y) ^ q) := by
  have hm : y ∈ Metric.eball (0 : ℝ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa [Real.dist_eq] using hy
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := q)).hasSum hm
  simpa [binomialSeries, FormalMultilinearSeries.ofScalars, List.prod_ofFn,
    Fin.prod_const, smul_eq_mul] using h

private theorem choose_succ_neg_of_pos (q : ℝ) (n : ℕ)
    (hqn : q < n) (hc : 0 < Ring.choose q n) : Ring.choose q (n + 1) < 0 := by
  have h := real_choose_mul_succ q n
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hm := mul_neg_of_neg_of_pos (sub_neg.mpr hqn) hc
  nlinarith

private theorem choose_succ_pos_of_neg (q : ℝ) (n : ℕ)
    (hqn : q < n) (hc : Ring.choose q n < 0) : 0 < Ring.choose q (n + 1) := by
  have h := real_choose_mul_succ q n
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hm := mul_pos_of_neg_of_neg (sub_neg.mpr hqn) hc
  nlinarith

/-- Strict alternating signs of the binomial tail in the entropy-order interval. -/
theorem real_choose_even_pos_odd_neg (q : ℝ) (hq₁ : 1 < q) (hq₂ : q < 2) (n : ℕ) :
    0 < Ring.choose q (2 * n + 2) ∧ Ring.choose q (2 * n + 3) < 0 := by
  induction n with
  | zero =>
      have h := real_choose_mul_succ q 1
      simp only [Nat.cast_one, Ring.choose_one_right] at h
      have hc : 0 < Ring.choose q 2 := by nlinarith [mul_pos (sub_pos.mpr hq₁) (by linarith : 0 < q)]
      exact ⟨hc, choose_succ_neg_of_pos q 2 (by simpa using hq₂) hc⟩
  | succ n ih =>
      have hn : q < (2 * n + 3 : ℕ) := by push_cast; nlinarith
      have ha := choose_succ_pos_of_neg q (2 * n + 3) hn ih.2
      have hn' : q < (2 * n + 3 + 1 : ℕ) := by push_cast; nlinarith
      have hb := choose_succ_neg_of_pos q (2 * n + 3 + 1) hn' ha
      convert And.intro ha hb using 1

/-- Every coefficient of the denominator correction is strictly positive. -/
theorem harmonicBinomialCoefficient_pos (q : ℝ) (hq₁ : 1 < q) (hq₂ : q < 2) (n : ℕ) :
    0 < harmonicBinomialCoefficient q n := by
  exact div_pos (neg_pos.mpr (real_choose_even_pos_odd_neg q hq₁ hq₂ n).2) (by linarith)

/-- The odd part of the actual binomial series. -/
theorem hasSum_real_binomial_odd (q y : ℝ) (hy : |y| < 1) :
    HasSum (fun n : ℕ => 2 * Ring.choose q (2 * n + 1) * y ^ (2 * n + 1))
      ((1 + y) ^ q - (1 - y) ^ q) := by
  let f : ℕ → ℝ := fun n => Ring.choose q n * y ^ n - Ring.choose q n * (-y) ^ n
  have hs : HasSum f ((1 + y) ^ q - (1 - y) ^ q) := by
    simpa only [f, sub_eq_add_neg] using
      (hasSum_real_binomial q y hy).sub (hasSum_real_binomial q (-y) (by simpa using hy))
  have ho := hs.summable.comp_injective
    (show Function.Injective (fun n : ℕ => 2 * n + 1) by intro a b h; dsimp at h; omega)
  have he : HasSum (fun n => f (2 * n)) 0 := by
    convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0) using 1
    ext n
    simp [f, Even.neg_pow (show Even (2 * n) by exact even_two_mul n)]
  have heo := he.even_add_odd ho.hasSum
  have heq := heo.unique hs
  simp only [zero_add] at heq
  rw [← heq]
  convert ho.hasSum using 1
  ext n
  have hn : Odd (2 * n + 1) := ⟨n, by omega⟩
  simp only [Function.comp_apply, f, hn.neg_pow]
  ring

/-- The positive denominator correction has its prescribed sum at every nonzero
point of the open interval; no coefficient-sign hypothesis is assumed. -/
theorem hasSum_harmonicBinomial_open (q y : ℝ) (hq : q ≠ 0)
    (hy : |y| < 1) (hy₀ : y ≠ 0) :
    HasSum (fun n : ℕ => harmonicBinomialCoefficient q n * y ^ (2 * n + 2))
      (1 - ((1 + y) ^ q - (1 - y) ^ q) / (2 * q * y)) := by
  have ho := hasSum_real_binomial_odd q y hy
  have ht := (hasSum_nat_add_iff' (f := fun n : ℕ =>
    2 * Ring.choose q (2 * n + 1) * y ^ (2 * n + 1)) 1).mpr ho
  simp only [Finset.sum_range_one, mul_zero, zero_add, Ring.choose_one_right, pow_one] at ht
  have hscaled := ht.mul_left (-1 / (2 * q * y))
  convert hscaled using 1
  · ext n
    have hn : 2 * (n + 1) + 1 = 2 * n + 2 + 1 := by omega
    rw [hn, pow_succ]
    unfold harmonicBinomialCoefficient
    have hn' : 2 * n + 2 + 1 = 2 * n + 3 := by omega
    rw [hn']
    field_simp
    ring
  · field_simp
    ring

/-- Nonnegativity persists at both endpoint entropy orders. -/
theorem harmonicBinomialCoefficient_nonneg (q : ℝ) (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2) (n : ℕ) :
    0 ≤ harmonicBinomialCoefficient q n := by
  rcases eq_or_lt_of_le hq₁ with h | h
  · subst q
    have hc := Ring.choose_natCast (R := ℝ) 1 (2 * n + 3)
    norm_num [Nat.choose_eq_zero_of_lt (by omega : 1 < 2 * n + 3)] at hc
    simp [harmonicBinomialCoefficient, hc]
  rcases eq_or_lt_of_le hq₂ with h' | h'
  · subst q
    have hc := Ring.choose_natCast (R := ℝ) 2 (2 * n + 3)
    norm_num [Nat.choose_eq_zero_of_lt (by omega : 2 < 2 * n + 3)] at hc
    simp [harmonicBinomialCoefficient, hc]
  exact (harmonicBinomialCoefficient_pos q h h' n).le

/-- Positivity of the denominator forces every finite correction sum to stay
below one, uniformly as the spatial variable approaches its outer endpoint. -/
theorem harmonicBinomial_partial_sum_le_one (q : ℝ) (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2)
    (s : Finset ℕ) : ∑ n ∈ s, harmonicBinomialCoefficient q n ≤ 1 := by
  have hlim : Tendsto (fun y : ℝ => ∑ n ∈ s, harmonicBinomialCoefficient q n * y ^ (2 * n + 2))
      (𝓝[<] 1) (𝓝 (∑ n ∈ s, harmonicBinomialCoefficient q n)) := by
    have h : ContinuousAt (fun y : ℝ => ∑ n ∈ s, harmonicBinomialCoefficient q n * y ^ (2 * n + 2)) 1 := by
      fun_prop
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
    with y hy₁ hy₀
  change y < 1 at hy₁
  have hy : |y| < 1 := by rw [abs_of_pos hy₀]; exact hy₁
  have hq : 0 < q := by linarith
  have hs := hasSum_harmonicBinomial_open q y (ne_of_gt hq) hy (ne_of_gt hy₀)
  have hb (n : ℕ) : 0 ≤ harmonicBinomialCoefficient q n * y ^ (2 * n + 2) :=
    mul_nonneg (harmonicBinomialCoefficient_nonneg q hq₁ hq₂ n) (pow_nonneg hy₀.le _)
  have hsum := Summable.sum_le_tsum s (fun n _ => hb n) hs.summable
  rw [hs.tsum_eq] at hsum
  have hd : 0 < (1 + y) ^ q - (1 - y) ^ q := by
    exact sub_pos.mpr (Real.rpow_lt_rpow (by linarith) (by linarith) hq)
  have hfrac : 0 ≤ ((1 + y) ^ q - (1 - y) ^ q) / (2 * q * y) := by positivity
  linarith

/-- The positive correction series converges absolutely at the outer endpoint. -/
theorem summable_harmonicBinomialCoefficient (q : ℝ) (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2) :
    Summable (harmonicBinomialCoefficient q) := by
  apply summable_of_sum_le (harmonicBinomialCoefficient_nonneg q hq₁ hq₂)
  exact harmonicBinomial_partial_sum_le_one q hq₁ hq₂

/-- Exact value of the correction sum at the endpoint. -/
theorem hasSum_harmonicBinomial_endpoint (q : ℝ) (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2) :
    HasSum (harmonicBinomialCoefficient q) (1 - (2 : ℝ) ^ q / (2 * q)) := by
  have hq : 0 < q := by linarith
  have hs := summable_harmonicBinomialCoefficient q hq₁ hq₂
  have ht : Tendsto (fun y : ℝ => ∑' n, harmonicBinomialCoefficient q n * y ^ (2 * n + 2))
      (𝓝[<] 1) (𝓝 (∑' n, harmonicBinomialCoefficient q n)) := by
    apply tendsto_tsum_of_dominated_convergence hs
    · intro n
      have hc : ContinuousAt (fun y : ℝ => harmonicBinomialCoefficient q n * y ^ (2 * n + 2)) 1 := by
        fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
        with y hy₁ hy₀ n
      have hb := harmonicBinomialCoefficient_nonneg q hq₁ hq₂ n
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hb (pow_nonneg hy₀.le _))]
      exact mul_le_of_le_one_right hb (pow_le_one₀ hy₀.le hy₁.le)
  have he : Tendsto (fun y : ℝ => 1 - ((1 + y) ^ q - (1 - y) ^ q) / (2 * q * y))
      (𝓝[<] 1) (𝓝 (1 - (2 : ℝ) ^ q / (2 * q))) := by
    have hc : ContinuousAt (fun y : ℝ => 1 - ((1 + y) ^ q - (1 - y) ^ q) / (2 * q * y)) 1 := by
      apply continuousAt_const.sub
      apply ContinuousAt.div
      · exact ((Real.continuous_rpow_const hq.le).continuousAt.comp
          (continuousAt_const.add continuousAt_id)).sub
          ((Real.continuous_rpow_const hq.le).continuousAt.comp
            (continuousAt_const.sub continuousAt_id))
      · fun_prop
      · positivity
    simpa [Real.zero_rpow (ne_of_gt hq), one_add_one_eq_two] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have heq : (fun y : ℝ => ∑' n, harmonicBinomialCoefficient q n * y ^ (2 * n + 2)) =ᶠ[𝓝[<] 1]
      (fun y => 1 - ((1 + y) ^ q - (1 - y) ^ q) / (2 * q * y)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds]
      with y hy₁ hy₀
    exact (hasSum_harmonicBinomial_open q y (ne_of_gt hq)
      (by rw [abs_of_pos hy₀]; exact hy₁) (ne_of_gt hy₀)).tsum_eq
  rw [← tendsto_nhds_unique ht (he.congr' heq.symm)]
  exact hs.hasSum

/-- The endpoint correction is strictly below one, leaving a positive geometric margin. -/
theorem harmonicBinomial_tsum_lt_one (q : ℝ) (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2) :
    (∑' n, harmonicBinomialCoefficient q n) < 1 := by
  rw [(hasSum_harmonicBinomial_endpoint q hq₁ hq₂).tsum_eq]
  have hq : 0 < q := by linarith
  have hfrac : 0 < (2 : ℝ) ^ q / (2 * q) := by positivity
  linarith

/-- The binomial correction as the sum of its nonnegative even monomials. -/
noncomputable def harmonicCorrection (q y : ℝ) : ℝ :=
  ∑' n, harmonicBinomialCoefficient q n * y ^ (2 * n + 2)

/-- Absolute summability throughout the closed spatial interval follows from
the already established endpoint majorant. -/
theorem summable_harmonicCorrection (q : ℝ) (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2)
    (y : ℝ) (hy : |y| ≤ 1) :
    Summable (fun n => harmonicBinomialCoefficient q n * y ^ (2 * n + 2)) := by
  apply (summable_harmonicBinomialCoefficient q hq₁ hq₂).of_norm_bounded
  intro n
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (harmonicBinomialCoefficient_nonneg q hq₁ hq₂ n),
    Real.norm_eq_abs, abs_pow]
  exact mul_le_of_le_one_right (harmonicBinomialCoefficient_nonneg q hq₁ hq₂ n)
    (pow_le_one₀ (abs_nonneg y) hy)

/-- Nonnegativity and the strict geometric margin hold uniformly, including endpoints. -/
theorem harmonicCorrection_bounds (q : ℝ) (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2)
    (y : ℝ) (hy : |y| ≤ 1) : 0 ≤ harmonicCorrection q y ∧ harmonicCorrection q y < 1 := by
  have hs := summable_harmonicCorrection q hq₁ hq₂ y hy
  have hb (n : ℕ) : 0 ≤ harmonicBinomialCoefficient q n * y ^ (2 * n + 2) :=
    mul_nonneg (harmonicBinomialCoefficient_nonneg q hq₁ hq₂ n)
      (Even.pow_nonneg (by exact ⟨n + 1, by omega⟩) _)
  refine ⟨tsum_nonneg hb, lt_of_le_of_lt ?_ (harmonicBinomial_tsum_lt_one q hq₁ hq₂)⟩
  apply hs.tsum_le_tsum _ (summable_harmonicBinomialCoefficient q hq₁ hq₂)
  intro n
  have he : y ^ (2 * n + 2) = |y| ^ (2 * n + 2) :=
    (Even.pow_abs (by exact ⟨n + 1, by omega⟩) y).symm
  rw [he]
  exact mul_le_of_le_one_right (harmonicBinomialCoefficient_nonneg q hq₁ hq₂ n)
    (pow_le_one₀ (abs_nonneg y) hy)

@[simp] theorem harmonicCorrection_zero (q : ℝ) : harmonicCorrection q 0 = 0 := by
  simp [harmonicCorrection]

/-- Exact correction identity on the closed interval away from the removable center. -/
theorem harmonicCorrection_eq (q : ℝ) (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2)
    (y : ℝ) (hy : |y| ≤ 1) (hy₀ : y ≠ 0) :
    harmonicCorrection q y = 1 - ((1 + y) ^ q - (1 - y) ^ q) / (2 * q * y) := by
  have hq : 0 < q := by linarith
  rcases eq_or_lt_of_le hy with he | he
  · have hycases : y = 1 ∨ y = -1 := by
      rcases le_total 0 y with hn | hn
      · rw [abs_of_nonneg hn] at he
        exact Or.inl he
      · rw [abs_of_nonpos hn] at he
        exact Or.inr (by linarith)
    rcases hycases with rfl | rfl
    · simpa [harmonicCorrection, Real.zero_rpow (ne_of_gt hq), one_add_one_eq_two]
        using (hasSum_harmonicBinomial_endpoint q hq₁ hq₂).tsum_eq
    · have hp (n : ℕ) : (-1 : ℝ) ^ (2 * n + 2) = 1 :=
        (show Even (2 * n + 2) from ⟨n + 1, by omega⟩).neg_one_pow
      simp only [harmonicCorrection, hp, mul_one,
        (hasSum_harmonicBinomial_endpoint q hq₁ hq₂).tsum_eq]
      norm_num [Real.zero_rpow (ne_of_gt hq)]
  · exact (hasSum_harmonicBinomial_open q y (ne_of_gt hq) he hy₀).tsum_eq

/-- The positive normalization of the even kernel. -/
noncomputable def harmonicEvenScale (q : ℝ) : ℝ := (2 : ℝ) ^ q / (2 * q)

theorem harmonicEvenScale_eq_center (q : ℝ) :
    harmonicEvenScale q = (2 : ℝ) ^ (q - 1) / q := by
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  unfold harmonicEvenScale
  ring

/-- The actual even kernel is the geometric inverse of its positive correction. -/
theorem harmonicEvenKernel_eq_geometric (q : ℝ) (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2)
    (x : ℝ) (hx : |x| ≤ 1 / 2) :
    harmonicEvenKernel q x = harmonicEvenScale q * (1 - harmonicCorrection q (2 * x))⁻¹ := by
  have hq : 0 < q := by linarith
  have hx' := abs_le.mp hx
  have hy : |2 * x| ≤ 1 := by rw [abs_mul]; norm_num; linarith
  by_cases hx₀ : x = 0
  · subst x
    simp [harmonicEvenKernel, harmonicEvenScale_eq_center]
  have hp : 0 ≤ 1 / 2 + x := by linarith
  have hm : 0 ≤ 1 / 2 - x := by linarith
  have hD : (1 / 2 + x) ^ q - (1 / 2 - x) ^ q ≠ 0 := by
    intro h
    have hi := (Real.rpow_left_inj hp hm (ne_of_gt hq)).mp (sub_eq_zero.mp h)
    exact hx₀ (by linarith)
  have hscale : (1 + 2 * x) ^ q - (1 - 2 * x) ^ q =
      (2 : ℝ) ^ q * ((1 / 2 + x) ^ q - (1 / 2 - x) ^ q) := by
    rw [show 1 + 2 * x = 2 * (1 / 2 + x) by ring,
      show 1 - 2 * x = 2 * (1 / 2 - x) by ring,
      Real.mul_rpow (by norm_num) hp, Real.mul_rpow (by norm_num) hm]
    ring
  rw [harmonicEvenKernel, ite_eq_right hx₀,
    harmonicCorrection_eq q hq₁ hq₂ (2 * x) hy (mul_ne_zero two_ne_zero hx₀),
    sub_sub_cancel, inv_div, hscale]
  unfold harmonicEvenScale
  have hs : (2 : ℝ) ^ q ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by norm_num) q)
  field_simp

/-- Coefficient of an actual even-kernel monomial, indexed by a finite binomial word. -/
noncomputable def harmonicEvenSeriesCoefficient (q : ℝ) (w : PositiveSeriesIndex) : ℝ :=
  harmonicEvenScale q * positiveWordCoefficient (harmonicBinomialCoefficient q) w.1 w.2 *
    (2 : ℝ) ^ (2 * positiveWordDegree w.1 w.2)

/-- Every coefficient in the actual harmonic even-kernel expansion is nonnegative. -/
theorem harmonicEvenSeriesCoefficient_nonneg (q : ℝ) (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2)
    (w : PositiveSeriesIndex) : 0 ≤ harmonicEvenSeriesCoefficient q w := by
  have hq : 0 < q := by linarith
  unfold harmonicEvenSeriesCoefficient harmonicEvenScale
  have hw := positiveWordCoefficient_nonneg (harmonicBinomialCoefficient q)
    (harmonicBinomialCoefficient_nonneg q hq₁ hq₂) w.1 w.2
  positivity

/-- Positive even-monomial expansion of the actual kernel, with rigorous
absolute convergence on the entire closed spatial interval. -/
theorem hasSum_harmonicEvenKernel (q : ℝ) (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2)
    (x : ℝ) (hx : |x| ≤ 1 / 2) :
    HasSum (fun w : PositiveSeriesIndex => harmonicEvenSeriesCoefficient q w *
      x ^ (2 * positiveWordDegree w.1 w.2)) (harmonicEvenKernel q x) := by
  have hy : |2 * x| ≤ 1 := by rw [abs_mul]; norm_num; linarith
  have hb := (summable_harmonicCorrection q hq₁ hq₂ (2 * x) hy).hasSum
  have hbounds := harmonicCorrection_bounds q hq₁ hq₂ (2 * x) hy
  have hg := hasSum_positiveWord_geometric (harmonicBinomialCoefficient q)
    (2 * x) (harmonicCorrection q (2 * x))
    (harmonicBinomialCoefficient_nonneg q hq₁ hq₂) hbounds.1 hbounds.2 hb
  rw [harmonicEvenKernel_eq_geometric q hq₁ hq₂ x hx]
  convert hg.mul_left (harmonicEvenScale q) using 1
  ext w
  simp only [harmonicEvenSeriesCoefficient, mul_pow]
  ring

/-- The endpoint coefficients sum to exactly one, yielding the common summable
majorant needed for all finite harmonic-lowering interchanges. -/
theorem hasSum_harmonicEvenKernel_endpoint (q : ℝ) (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2) :
    HasSum (fun w : PositiveSeriesIndex => harmonicEvenSeriesCoefficient q w *
      (1 / 2 : ℝ) ^ (2 * positiveWordDegree w.1 w.2)) 1 := by
  have hq : q ≠ 0 := by linarith
  have h := hasSum_harmonicEvenKernel q hq₁ hq₂ (1 / 2) (by norm_num)
  norm_num [harmonicEvenKernel, Real.zero_rpow hq] at h
  exact h

end RenyiMonotonicity
