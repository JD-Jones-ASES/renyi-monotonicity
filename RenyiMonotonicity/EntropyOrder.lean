module

public import RenyiMonotonicity.CoefficientLemmas

@[expose] public section

open scoped BigOperators Topology
open Filter

namespace RenyiMonotonicity

/-- Rényi and Tsallis order comparisons agree at each fixed positive order. -/
theorem renyi_le_iff_tsallis_le {m l : ℕ} (q : ℝ) (g : Fin m → ℝ) (h : Fin l → ℝ)
    (hq : 0 < q) (hg : 0 < powerSum q g) (hh : 0 < powerSum q h) :
    renyi q g ≤ renyi q h ↔ tsallis q g ≤ tsallis q h := by
  by_cases hq1 : q = 1
  · simp [hq1]
  · simp only [renyi, tsallis, ne_of_gt hq, hq1, ↓reduceIte]
    rcases lt_or_gt_of_ne hq1 with hlow | hhigh
    · rw [div_le_div_iff_of_pos_right (sub_pos.mpr hlow),
        div_le_div_iff_of_pos_right (sub_pos.mpr hlow),
        Real.log_le_log_iff hg hh]
      exact sub_le_sub_iff_right 1 |>.symm
    · rw [div_le_div_right_of_neg (sub_neg.mpr hhigh),
        div_le_div_right_of_neg (sub_neg.mpr hhigh),
        Real.log_le_log_iff hh hg]
      exact sub_le_sub_iff_right 1 |>.symm

/-- Every individual coefficient depends continuously on all coin parameters. -/
theorem continuous_bernoulliSum_coordinate {n : ℕ} (k : Fin (n + 1)) :
    Continuous (fun p : Fin n → ℝ => bernoulliSum p k) := by
  simp_rw [bernoulliSum_eq_sum_weights, bernoulliWeight]
  fun_prop

theorem continuous_bernoulliSum {n : ℕ} :
    Continuous (fun p : Fin n → ℝ => bernoulliSum p) := by
  apply continuous_pi
  intro k
  exact continuous_bernoulliSum_coordinate k

/-- Power sums are jointly continuous in the law and order at every positive order,
even when some atoms vanish. -/
theorem continuousAt_powerSum_joint {m : ℕ} (q : ℝ) (g : Fin m → ℝ) (hq : 0 < q) :
    ContinuousAt (fun z : ℝ × (Fin m → ℝ) => powerSum z.1 z.2) (q, g) := by
  unfold powerSum
  apply tendsto_finsetSum
  intro k _
  change ContinuousAt (fun z : ℝ × (Fin m → ℝ) => (z.2 k) ^ z.1) (q, g)
  have hpair : ContinuousAt (fun z : ℝ × (Fin m → ℝ) => (z.2 k, z.1)) (q, g) := by
    fun_prop
  exact ContinuousAt.comp (f := fun z : ℝ × (Fin m → ℝ) => (z.2 k, z.1))
    (Real.continuousAt_rpow_of_pos (g k, q) hq) hpair

/-- Uniform positive order bands avoid the discontinuity of zero to the zeroth power. -/
theorem continuousOn_powerSum_positive {m : ℕ} :
    ContinuousOn (fun z : ℝ × (Fin m → ℝ) => powerSum z.1 z.2) {z | 0 < z.1} := by
  intro z hz
  exact (continuousAt_powerSum_joint z.1 z.2 hz).continuousWithinAt

@[simp] theorem powerSum_one {m : ℕ} (g : Fin m → ℝ) : powerSum 1 g = ∑ k, g k := by
  simp [powerSum]

/-- Differentiation in the order at one includes a zero atom by local constancy. -/
theorem hasDerivAt_rpow_order_one (a : ℝ) (ha : 0 ≤ a) :
    HasDerivAt (fun q : ℝ => a ^ q) (a * Real.log a) 1 := by
  rcases eq_or_lt_of_le ha with hzero | hpos
  · have haz : a = 0 := hzero.symm
    subst a
    have heq : (fun q : ℝ => (0 : ℝ) ^ q) =ᶠ[𝓝 (1 : ℝ)] (fun _ => 0) := by
      filter_upwards [eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0)] with q hq
      exact Real.zero_rpow hq
    simpa using (hasDerivAt_const (1 : ℝ) (0 : ℝ)).congr_of_eventuallyEq heq
  · simpa [mul_comm] using (hasDerivAt_id (1 : ℝ)).const_rpow hpos

/-- The order derivative of a finite nonnegative power sum is minus Shannon entropy. -/
theorem hasDerivAt_powerSum_order_one {m : ℕ} (g : Fin m → ℝ)
    (hg : ∀ k, 0 ≤ g k) :
    HasDerivAt (fun q : ℝ => powerSum q g) (-shannon g) 1 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun k _ => hasDerivAt_rpow_order_one (g k) (hg k))
  simpa [powerSum, shannon, Real.negMulLog_eq_neg] using h

/-- The logarithmic power sum has the same order derivative at one for a probability law. -/
theorem hasDerivAt_log_powerSum_order_one {m : ℕ} (g : Fin m → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hsum : ∑ k, g k = 1) :
    HasDerivAt (fun q : ℝ => Real.log (powerSum q g)) (-shannon g) 1 := by
  have hone : powerSum 1 g = 1 := by simpa using hsum
  simpa [hone] using (hasDerivAt_powerSum_order_one g hg).log (by rw [hone]; norm_num)

/-- The ordinary Tsallis quotient tends to Shannon entropy through the punctured order limit. -/
theorem tendsto_tsallis_formula_one {m : ℕ} (g : Fin m → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hsum : ∑ k, g k = 1) :
    Tendsto (fun q : ℝ => (powerSum q g - 1) / (1 - q)) (𝓝[≠] 1) (𝓝 (shannon g)) := by
  have heq : (fun q : ℝ => (powerSum q g - 1) / (1 - q)) =
      fun q => -slope (fun u => powerSum u g) 1 q := by
    funext q
    rw [slope_def_field, powerSum_one, hsum, show 1 - q = -(q - 1) by ring, div_neg]
  rw [heq]
  simpa only [neg_neg] using (hasDerivAt_powerSum_order_one g hg).tendsto_slope.neg

/-- The ordinary Rényi quotient has the same punctured order limit. -/
theorem tendsto_renyi_formula_one {m : ℕ} (g : Fin m → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hsum : ∑ k, g k = 1) :
    Tendsto (fun q : ℝ => Real.log (powerSum q g) / (1 - q))
      (𝓝[≠] 1) (𝓝 (shannon g)) := by
  have heq : (fun q : ℝ => Real.log (powerSum q g) / (1 - q)) =
      fun q => -slope (fun u => Real.log (powerSum u g)) 1 q := by
    funext q
    rw [slope_def_field, powerSum_one, hsum, Real.log_one, sub_zero,
      show 1 - q = -(q - 1) by ring, div_neg]
  rw [heq]
  simpa only [neg_neg] using (hasDerivAt_log_powerSum_order_one g hg hsum).tendsto_slope.neg

/-- The explicit Tsallis endpoint branch is continuous in the order at one. -/
theorem continuousAt_tsallis_order_one {m : ℕ} (g : Fin m → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hsum : ∑ k, g k = 1) :
    ContinuousAt (fun q : ℝ => tsallis q g) 1 := by
  rw [continuousAt_iff_punctured_nhds, tsallis_one]
  have hne1 : ∀ᶠ q : ℝ in 𝓝[≠] 1, q ≠ 1 := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact hq
  have hne0 : ∀ᶠ q : ℝ in 𝓝[≠] 1, q ≠ 0 :=
    (eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0)).filter_mono nhdsWithin_le_nhds
  apply (tendsto_tsallis_formula_one g hg hsum).congr'
  filter_upwards [hne1, hne0] with q hq1 hq0
  simp [tsallis, hq0, hq1]

/-- The explicit Rényi endpoint branch is continuous in the order at one. -/
theorem continuousAt_renyi_order_one {m : ℕ} (g : Fin m → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hsum : ∑ k, g k = 1) :
    ContinuousAt (fun q : ℝ => renyi q g) 1 := by
  rw [continuousAt_iff_punctured_nhds, renyi_one]
  have hne1 : ∀ᶠ q : ℝ in 𝓝[≠] 1, q ≠ 1 := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact hq
  have hne0 : ∀ᶠ q : ℝ in 𝓝[≠] 1, q ≠ 0 :=
    (eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0)).filter_mono nhdsWithin_le_nhds
  apply (tendsto_renyi_formula_one g hg hsum).congr'
  filter_upwards [hne1, hne0] with q hq1 hq0
  simp [renyi, hq0, hq1]

/-- Full order limit of the public Tsallis definition, including zero masses. -/
theorem tendsto_tsallis_order_one {m : ℕ} (g : Fin m → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hsum : ∑ k, g k = 1) :
    Tendsto (fun q : ℝ => tsallis q g) (𝓝 1) (𝓝 (shannon g)) := by
  simpa only [tsallis_one] using (continuousAt_tsallis_order_one g hg hsum).tendsto

/-- Full order limit of the public Rényi definition, including zero masses. -/
theorem tendsto_renyi_order_one {m : ℕ} (g : Fin m → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hsum : ∑ k, g k = 1) :
    Tendsto (fun q : ℝ => renyi q g) (𝓝 1) (𝓝 (shannon g)) := by
  simpa only [renyi_one] using (continuousAt_renyi_order_one g hg hsum).tendsto

/-- A normalized nonnegative finite law has a positive power sum at every real order. -/
theorem powerSum_pos {m : ℕ} (q : ℝ) (g : Fin m → ℝ)
    (hg : ∀ k, 0 ≤ g k) (hsum : ∑ k, g k = 1) : 0 < powerSum q g := by
  have hspos : 0 < ∑ k, g k := by rw [hsum]; norm_num
  obtain ⟨k, hk, hkg⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun k _ => hg k)).mp hspos
  apply (Finset.sum_pos_iff_of_nonneg (fun k _ => Real.rpow_nonneg (hg k) q)).mpr
  exact ⟨k, hk, Real.rpow_pos_of_pos hkg q⟩

/-- The entropy comparison equivalence for ordinary finite probability laws. -/
theorem renyi_le_iff_tsallis_le_probability {m l : ℕ} (q : ℝ)
    (g : Fin m → ℝ) (h : Fin l → ℝ) (hq : 0 < q)
    (hg : ∀ k, 0 ≤ g k) (hh : ∀ k, 0 ≤ h k)
    (hgsum : ∑ k, g k = 1) (hhsum : ∑ k, h k = 1) :
    renyi q g ≤ renyi q h ↔ tsallis q g ≤ tsallis q h :=
  renyi_le_iff_tsallis_le q g h hq (powerSum_pos q g hg hgsum) (powerSum_pos q h hh hhsum)

theorem continuousAt_powerSum_bernoulli_joint {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hq : 0 < q) :
    ContinuousAt (fun z : ℝ × (Fin n → ℝ) => powerSum z.1 (bernoulliSum z.2)) (q, p) := by
  exact ContinuousAt.comp (x := (q, p)) (f := fun z : ℝ × (Fin n → ℝ) => (z.1, bernoulliSum z.2))
    (continuousAt_powerSum_joint q (bernoulliSum p) hq)
    (continuousAt_fst.prodMk (continuous_bernoulliSum.continuousAt.comp continuousAt_snd))

theorem continuousAt_powerSum_bernoulli {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hq : 0 < q) : ContinuousAt (fun r => powerSum q (bernoulliSum r)) p := by
  exact ContinuousAt.comp (f := fun r : Fin n → ℝ => (q, r))
    (continuousAt_powerSum_bernoulli_joint q p hq) (continuousAt_const.prodMk continuousAt_id)

/-- Positive-order Tsallis entropy is continuous through support-changing parameter faces. -/
theorem continuousAt_tsallis_bernoulli {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hq : 0 < q) : ContinuousAt (fun r => tsallis q (bernoulliSum r)) p := by
  by_cases hq1 : q = 1
  · simp only [hq1, tsallis_one, shannon]
    apply tendsto_finsetSum
    intro k _
    exact Real.continuous_negMulLog.continuousAt.comp
      (continuous_bernoulliSum_coordinate k).continuousAt
  · simp only [tsallis, ne_of_gt hq, hq1, ↓reduceIte]
    exact ((continuousAt_powerSum_bernoulli q p hq).sub continuousAt_const).div_const _

/-- Positive-order Rényi entropy is continuous through support-changing cube faces. -/
theorem continuousAt_renyi_bernoulli {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hq : 0 < q) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    ContinuousAt (fun r => renyi q (bernoulliSum r)) p := by
  by_cases hq1 : q = 1
  · simp only [hq1, renyi_one, shannon]
    apply tendsto_finsetSum
    intro k _
    exact Real.continuous_negMulLog.continuousAt.comp
      (continuous_bernoulliSum_coordinate k).continuousAt
  · simp only [renyi, ne_of_gt hq, hq1, ↓reduceIte]
    apply ContinuousAt.div_const
    apply ContinuousAt.log (continuousAt_powerSum_bernoulli q p hq)
    exact ne_of_gt (powerSum_pos q (bernoulliSum p)
      (bernoulliSum_nonneg p hp hp1) (sum_bernoulliSum p))

end RenyiMonotonicity
