module

public import RenyiMonotonicity.HarmonicBernoulli
public import RenyiMonotonicity.NormalizedMidpoint

@[expose] public section

open scoped Topology
open Filter

namespace RenyiMonotonicity
namespace HarmonicSequence

/-- Finite summation by parts for arbitrary index weights, including both
outer fluxes. -/
theorem sum_lowerFlux_index {n : ℕ} (s : HarmonicSequence (n + 1))
    (q : ℝ) (hq : 0 < q) (F : ℕ → ℝ) :
    (∑ k ∈ Finset.range (n + 2), s.lowerFlux q k * F k) =
      ∑ k ∈ Finset.range (n + 1), s.lower.mass k ^ q * (F (k + 1) - F k) := by
  simp only [lowerFlux, sub_mul, Finset.sum_sub_distrib]
  have hl : (∑ k ∈ Finset.range (n + 2), (s.mass k * s.node k) ^ q * F k) =
      ∑ k ∈ Finset.range (n + 1), s.lower.mass k ^ q * F (k + 1) := by
    rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ']
    simp only [s.node_zero, mul_zero, Real.zero_rpow (ne_of_gt hq), zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    rw [lower_mass, s.balance k (by simpa only [Finset.mem_range] using hk)]
  have hr : (∑ k ∈ Finset.range (n + 2), (s.mass k * (1 - s.node (k + 1))) ^ q * F k) =
      ∑ k ∈ Finset.range (n + 1), s.lower.mass k ^ q * F k := by
    rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ]
    simp only [s.node_last, sub_self, mul_zero, Real.zero_rpow (ne_of_gt hq), zero_mul, add_zero]
    rfl
  rw [hl, hr, ← Finset.sum_sub_distrib]
  simp only [mul_sub]

/-- The cubic harmonic moment is exactly a positive weighted sum of the
drops in successive mixing-grid gaps. -/
theorem moment_one_one_eq {n : ℕ} (s : HarmonicSequence (n + 1)) :
    s.moment 1 1 = ∑ k ∈ Finset.range (n + 1),
      s.lower.mass k * (s.gap (k + 1) - s.gap k) := by
  have hid : s.moment 1 1 =
      ∑ k ∈ Finset.range (n + 2), s.lowerFlux 1 k * s.gap k := by
    unfold moment functional
    apply Finset.sum_congr rfl
    intro k hk
    simp only [lowerFlux, Real.rpow_one, center, gap]
    norm_num
    ring
  rw [hid, s.sum_lowerFlux_index 1 (by norm_num)]
  simp only [Real.rpow_one]

/-- One strictly decreasing gap already makes the first nonconstant moment
strictly negative. -/
theorem moment_one_one_neg {n : ℕ} (s : HarmonicSequence (n + 1))
    (hstrict : s.gap 1 < s.gap 0) : s.moment 1 1 < 0 := by
  rw [s.moment_one_one_eq]
  apply Finset.sum_neg'
  · intro k hk
    have hk' : k ≤ n := by simp only [Finset.mem_range] at hk; omega
    exact mul_nonpos_of_nonneg_of_nonpos (s.lower.mass_pos k hk').le
      (sub_nonpos.mpr (s.gap_antitone (by omega) (by omega)))
  · refine ⟨0, by simp, ?_⟩
    exact mul_neg_of_pos_of_neg (s.lower.mass_pos 0 (by omega)) (sub_neg.mpr hstrict)

/-- A convergent nonnegative even expansion can be bounded above by any one
of its moment terms, since all the remaining moments are nonpositive. -/
theorem functional_le_evenSeries_term {ι : Type*} {n : ℕ} (s : HarmonicSequence n) (q : ℝ)
    (F : ℝ → ℝ) (c : ι → ℝ) (degree : ι → ℕ)
    (hc : ∀ i, 0 ≤ c i)
    (hseries : ∀ x : ℝ, |x| ≤ 1 / 2 → HasSum (fun i => c i * x ^ (2 * degree i)) (F x))
    (hmoment : ∀ m : ℕ, s.moment q m ≤ 0) (i₀ : ι) :
    s.functional q F ≤ c i₀ * s.moment q (degree i₀) := by
  classical
  have hs : HasSum (fun i => c i * s.moment q (degree i)) (s.functional q F) := by
    have hterms : ∀ k ∈ Finset.range (n + 1),
        HasSum (fun i => s.mass k ^ q *
          (c i * s.center (k + 1) ^ (2 * degree i) - c i * s.center k ^ (2 * degree i)))
          (s.mass k ^ q * (F (s.center (k + 1)) - F (s.center k))) := by
      intro k hk
      have hk' : k ≤ n := by simp only [Finset.mem_range] at hk; omega
      exact ((hseries (s.center (k + 1)) (s.abs_center_le (by omega))).sub
        (hseries (s.center k) (s.abs_center_le (by omega)))).mul_left (s.mass k ^ q)
    convert hasSum_sum hterms using 1
    · ext i
      unfold moment functional
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    · rfl
  have hsone : HasSum (fun i : ι => if i = i₀ then c i₀ * s.moment q (degree i₀) else 0)
      (c i₀ * s.moment q (degree i₀)) := hasSum_ite_eq i₀ _
  apply hasSum_le _ hs hsone
  intro i
  split_ifs with hi
  · subst i; rfl
  · exact mul_nonpos_of_nonneg_of_nonpos (hc i) (hmoment (degree i))

/-- Isolating the first positive-degree word of the actual harmonic series. -/
theorem harmonicFunctional_le_cubic {n : ℕ} (s : HarmonicSequence n) (q : ℝ)
    (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2) :
    s.functional q (harmonicEvenKernel q) ≤
      (4 * harmonicEvenScale q * harmonicBinomialCoefficient q 0) * s.moment q 1 := by
  have h := s.functional_le_evenSeries_term q (harmonicEvenKernel q)
    (harmonicEvenSeriesCoefficient q) (fun w => positiveWordDegree w.1 w.2)
    (harmonicEvenSeriesCoefficient_nonneg q hq₁ hq₂)
    (hasSum_harmonicEvenKernel q hq₁ hq₂) (moment_nonpos q hq₁ hq₂ s)
    (⟨1, (0, ())⟩ : PositiveSeriesIndex)
  norm_num [harmonicEvenSeriesCoefficient, positiveWordDegree, positiveWordCoefficient,
    mul_comm, mul_left_comm, mul_assoc] at h ⊢
  exact h

end HarmonicSequence

/-- The first denominator correction is an explicit quadratic in the order. -/
theorem harmonicBinomialCoefficient_zero (q : ℝ) (hq : q ≠ 0) :
    harmonicBinomialCoefficient q 0 = -(q - 1) * (q - 2) / 6 := by
  have h₂ := real_choose_mul_succ q 1
  have h₃ := real_choose_mul_succ q 2
  norm_num only [Nat.cast_one, Nat.cast_ofNat, Ring.choose_one_right] at h₂ h₃
  have hc₂ : Ring.choose q 2 = (q - 1) * q / 2 := by linarith
  have hc₃ : Ring.choose q 3 = (q - 2) * ((q - 1) * q / 2) / 3 := by rw [hc₂] at h₃; linarith
  simp only [harmonicBinomialCoefficient, mul_zero, zero_add, hc₃]
  field_simp
  ring

/-- The removable normalized cubic coefficient has an elementary continuous
form at order one. -/
theorem harmonicCubicCoefficient_normalized (q : ℝ) (hq : q ≠ 0) (hq₁ : q ≠ 1) :
    (4 * harmonicEvenScale q * harmonicBinomialCoefficient q 0) / (1 - q) =
      (2 / 3) * harmonicEvenScale q * (q - 2) := by
  rw [harmonicBinomialCoefficient_zero q hq]
  have hd : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq₁)
  field_simp
  ring

/-- Strict cubic negativity follows from actual Hillion--Johnson curvature,
with no equality classification assumed for the finite-sequence theorem. -/
theorem bernoulli_harmonic_cubic_neg {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1 / 2)
    (hbiased : ∃ i, p i < 1 / 2) :
    (bernoulliHarmonicSequence p hp hpHalf).moment 1 1 < 0 := by
  cases n with
  | zero => obtain ⟨i, hi⟩ := hbiased; exact Fin.elim0 i
  | succ n =>
    apply HarmonicSequence.moment_one_one_neg
    have h := mixingCoefficient_gap_strict_antitone_step p hp hpHalf hbiased 0 (by omega) (by omega)
    simpa [HarmonicSequence.gap] using h

/-- Finite harmonic moments are continuous in the entropy order at one,
including arbitrary finite-sequence masses. -/
theorem continuousAt_harmonicMoment_one {n : ℕ} (s : HarmonicSequence n) (m : ℕ) :
    ContinuousAt (fun q : ℝ => s.moment q m) 1 := by
  unfold HarmonicSequence.moment HarmonicSequence.functional
  apply tendsto_finsetSum
  intro k hk
  have hp : ContinuousAt (fun q : ℝ => s.mass k ^ q) 1 :=
    (Real.continuousAt_rpow_of_pos (s.mass k, 1) (by norm_num)).comp
      (continuousAt_const.prodMk continuousAt_id)
  exact hp.mul continuousAt_const

/-- A quantitative Shannon lower bound obtained by retaining one actual
positive even-series coefficient and taking the normalized order-one limit.
This avoids differentiating an infinite series. -/
theorem normalizedMidpointFunctional_one_ge_cubic {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1 / 2) :
    -(2 / 3) * (bernoulliHarmonicSequence p hp hpHalf).moment 1 1 ≤
      normalizedMidpointFunctional 1 p := by
  let s := bernoulliHarmonicSequence p hp hpHalf
  have hineq (q : ℝ) (hq₁ : 1 < q) (hq₂ : q ≤ 2) :
      ((2 / 3) * harmonicEvenScale q * (q - 2)) * s.moment q 1 ≤
        normalizedMidpointFunctional q p := by
    rw [normalizedMidpointFunctional_eq q p (ne_of_gt hq₁) (fun i => (hp i).le)
      (fun i => by linarith [hpHalf i]), midpointFunctional_eq_harmonicFunctional p hp hpHalf q (by linarith)]
    change _ ≤ s.functional q (harmonicEvenKernel q) / (1 - q)
    calc
      ((2 / 3) * harmonicEvenScale q * (q - 2)) * s.moment q 1 =
          ((4 * harmonicEvenScale q * harmonicBinomialCoefficient q 0) * s.moment q 1) / (1 - q) := by
        rw [← harmonicCubicCoefficient_normalized q (by linarith) (ne_of_gt hq₁)]
        ring
      _ ≤ s.functional q (harmonicEvenKernel q) / (1 - q) :=
        (div_le_div_right_of_neg (by linarith : 1 - q < 0)).mpr
          (s.harmonicFunctional_le_cubic q hq₁.le hq₂)
  have hscale : ContinuousAt harmonicEvenScale 1 := by
    unfold harmonicEvenScale
    fun_prop (disch := norm_num)
  have hleft : ContinuousAt (fun q : ℝ =>
      ((2 / 3) * harmonicEvenScale q * (q - 2)) * s.moment q 1) 1 :=
    ((continuousAt_const.mul hscale).mul (continuousAt_id.sub continuousAt_const)).mul
      (continuousAt_harmonicMoment_one s 1)
  have hright : ContinuousAt (fun q : ℝ => normalizedMidpointFunctional q p) 1 :=
    ContinuousAt.comp (x := 1) (f := fun q : ℝ => (q, p))
      (continuousAt_normalizedMidpointFunctional 1 p
        (edgeSum_pos p hp (fun i => by linarith [hpHalf i])))
      (continuousAt_id.prodMk continuousAt_const)
  have hl : Tendsto (fun q : ℝ => ((2 / 3) * harmonicEvenScale q * (q - 2)) * s.moment q 1)
      (𝓝[>] 1) (𝓝 (-(2 / 3) * s.moment 1 1)) := by
    convert hleft.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ))) using 1
    norm_num [harmonicEvenScale]
  apply le_of_tendsto_of_tendsto hl
    (hright.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ))))
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds] with q hq₁ hq₂
  exact hineq q hq₁ hq₂.le

/-- Strict Shannon midpoint positivity for every positive half-cube law with
at least one biased coin. All ingredients are proved for the actual masses. -/
theorem normalizedMidpointFunctional_one_pos {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1 / 2)
    (hbiased : ∃ i, p i < 1 / 2) : 0 < normalizedMidpointFunctional 1 p := by
  have hk := bernoulli_harmonic_cubic_neg p hp hpHalf hbiased
  have hb := normalizedMidpointFunctional_one_ge_cubic p hp hpHalf
  linarith

/-- The strict logarithmic form required by normalized first-contact localization. -/
theorem shannon_midpoint_strict {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hpHalf : ∀ i, p i ≤ 1 / 2)
    (hbiased : ∃ i, p i < 1 / 2) :
    0 < -∑ k : Fin (n + 2), edgeDifference p k * Real.log (edgeSum p k) := by
  simpa only [normalizedMidpointFunctional_one] using
    normalizedMidpointFunctional_one_pos p hp hpHalf hbiased

end RenyiMonotonicity
