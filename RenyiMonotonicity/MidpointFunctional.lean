module

public import RenyiMonotonicity.EntropyOrder
public import RenyiMonotonicity.EntropyCalculus
public import RenyiMonotonicity.CoordinateLaw

@[expose] public section

open scoped BigOperators Topology
open Filter

namespace RenyiMonotonicity

/-- Adjacent mass sum on the entire edge support, including both outer edges. -/
noncomputable def edgeSum {n : ℕ} (p : Fin n → ℝ) (k : Fin (n + 2)) : ℝ :=
  bernoulliMass p ((k.val : ℤ) - 1) + bernoulliMass p (k.val : ℤ)

/-- Adjacent mass difference, with integer subtraction before zero extension. -/
noncomputable def edgeDifference {n : ℕ} (p : Fin n → ℝ) (k : Fin (n + 2)) : ℝ :=
  bernoulliMass p ((k.val : ℤ) - 1) - bernoulliMass p (k.val : ℤ)

/-- The actual Poisson-binomial midpoint functional. A zero pair contributes zero. -/
noncomputable def midpointFunctional {n : ℕ} (q : ℝ) (p : Fin n → ℝ) : ℝ :=
  ∑ k : Fin (n + 2), edgeDifference p k * (edgeSum p k) ^ (q - 1)

theorem edgeSum_nonneg {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (k : Fin (n + 2)) : 0 ≤ edgeSum p k :=
  add_nonneg (bernoulliMass_nonneg p hp hp1 _) (bernoulliMass_nonneg p hp hp1 _)

theorem abs_edgeDifference_le_edgeSum {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (k : Fin (n + 2)) :
    |edgeDifference p k| ≤ edgeSum p k := by
  have ha := bernoulliMass_nonneg p hp hp1 ((k.val : ℤ) - 1)
  have hb := bernoulliMass_nonneg p hp hp1 (k.val : ℤ)
  dsimp [edgeDifference, edgeSum]
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- Scalar domination used to handle the negative exponent at a vanishing adjacent pair. -/
theorem abs_mul_rpow_sub_one_le (q d s : ℝ) (hq : 0 < q) (hs : 0 ≤ s)
    (hd : |d| ≤ s) : |d * s ^ (q - 1)| ≤ s ^ q := by
  rcases eq_or_lt_of_le hs with heq | hpos
  · have hs0 : s = 0 := heq.symm
    have hd0 : d = 0 := abs_eq_zero.mp (le_antisymm (by simpa [hs0] using hd) (abs_nonneg d))
    simp [hs0, hd0, Real.zero_rpow (ne_of_gt hq)]
  · rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hs _)]
    calc
      |d| * s ^ (q - 1) ≤ s * s ^ (q - 1) :=
        mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg hs _)
      _ = s ^ q := by
        nth_rw 1 [← Real.rpow_one s]
        rw [← Real.rpow_add hpos]
        congr 1
        ring

theorem abs_midpoint_summand_le {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hq : 0 < q) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (k : Fin (n + 2)) :
    |edgeDifference p k * (edgeSum p k) ^ (q - 1)| ≤ (edgeSum p k) ^ q :=
  abs_mul_rpow_sub_one_le q _ _ hq (edgeSum_nonneg p hp hp1 k)
    (abs_edgeDifference_le_edgeSum p hp hp1 k)

theorem continuous_bernoulliMass_coordinate {n : ℕ} (k : ℤ) :
    Continuous (fun p : Fin n → ℝ => bernoulliMass p k) := by
  simp only [bernoulliMass]
  split_ifs
  · simp_rw [coeff_bernoulliPolynomial, bernoulliWeight]
    fun_prop
  · fun_prop

theorem continuous_edgeSum {n : ℕ} (k : Fin (n + 2)) :
    Continuous (fun p : Fin n → ℝ => edgeSum p k) :=
  (continuous_bernoulliMass_coordinate _).add (continuous_bernoulliMass_coordinate _)

theorem continuous_edgeDifference {n : ℕ} (k : Fin (n + 2)) :
    Continuous (fun p : Fin n → ℝ => edgeDifference p k) :=
  (continuous_bernoulliMass_coordinate _).sub (continuous_bernoulliMass_coordinate _)

/-- Joint continuity of a single actual midpoint summand on the probability cube.
The zero-pair case uses domination by `s^q`, not negative-power continuity. -/
theorem continuousWithinAt_midpoint_summand {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hq : 0 < q) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (k : Fin (n + 2)) :
    ContinuousWithinAt
      (fun z : ℝ × (Fin n → ℝ) => edgeDifference z.2 k * (edgeSum z.2 k) ^ (z.1 - 1))
      {z | 0 < z.1 ∧ ∀ i, z.2 i ∈ Set.Icc (0 : ℝ) 1} (q, p) := by
  have hd : ContinuousAt (fun z : ℝ × (Fin n → ℝ) => edgeDifference z.2 k) (q, p) :=
    (continuous_edgeDifference k).continuousAt.comp continuousAt_snd
  have hs : ContinuousAt (fun z : ℝ × (Fin n → ℝ) => edgeSum z.2 k) (q, p) :=
    (continuous_edgeSum k).continuousAt.comp continuousAt_snd
  by_cases hz : edgeSum p k = 0
  · have hd0 : edgeDifference p k = 0 := abs_eq_zero.mp
      (le_antisymm (by simpa [hz] using abs_edgeDifference_le_edgeSum p hp hp1 k) (abs_nonneg _))
    change Tendsto _ _ (𝓝 (edgeDifference p k * (edgeSum p k) ^ (q - 1)))
    rw [hd0, zero_mul]
    apply squeeze_zero_norm' (a := fun z : ℝ × (Fin n → ℝ) => (edgeSum z.2 k) ^ z.1)
    · filter_upwards [self_mem_nhdsWithin] with z hzin
      simpa only [Real.norm_eq_abs] using abs_midpoint_summand_le z.1 z.2 hzin.1
        (fun i => (hzin.2 i).1) (fun i => (hzin.2 i).2) k
    · have hpow : ContinuousAt (fun z : ℝ × (Fin n → ℝ) => (edgeSum z.2 k) ^ z.1) (q, p) :=
        ContinuousAt.comp (x := (q, p))
          (f := fun z : ℝ × (Fin n → ℝ) => (edgeSum z.2 k, z.1))
          (Real.continuousAt_rpow_of_pos (edgeSum p k, q) hq) (hs.prodMk continuousAt_fst)
      simpa only [hz, Real.zero_rpow (ne_of_gt hq)] using
        (hpow.tendsto.mono_left (nhdsWithin_le_nhds
          (s := {z : ℝ × (Fin n → ℝ) | 0 < z.1 ∧ ∀ i, z.2 i ∈ Set.Icc (0 : ℝ) 1})))
  · have hpow : ContinuousAt
        (fun z : ℝ × (Fin n → ℝ) => (edgeSum z.2 k) ^ (z.1 - 1)) (q, p) :=
      ContinuousAt.comp (x := (q, p))
        (f := fun z : ℝ × (Fin n → ℝ) => (edgeSum z.2 k, z.1 - 1))
        (Real.continuousAt_rpow_of_ne (edgeSum p k, q - 1) hz)
        (hs.prodMk (continuousAt_fst.sub continuousAt_const))
    exact (hd.mul hpow).continuousWithinAt

/-- Joint midpoint continuity for every positive order, through every support-changing face. -/
theorem continuousOn_midpointFunctional_positive {n : ℕ} :
    ContinuousOn (fun z : ℝ × (Fin n → ℝ) => midpointFunctional z.1 z.2)
      {z | 0 < z.1 ∧ ∀ i, z.2 i ∈ Set.Icc (0 : ℝ) 1} := by
  intro z hz
  unfold midpointFunctional
  apply tendsto_finsetSum
  intro k _
  exact continuousWithinAt_midpoint_summand z.1 z.2 hz.1
    (fun i => (hz.2 i).1) (fun i => (hz.2 i).2) k

/-- The same joint continuity restricted to the closed parameter half cube. -/
theorem continuousOn_midpointFunctional_halfCube {n : ℕ} :
    ContinuousOn (fun z : ℝ × (Fin n → ℝ) => midpointFunctional z.1 z.2)
      {z | 0 < z.1 ∧ ∀ i, z.2 i ∈ Set.Icc (0 : ℝ) (1 / 2)} := by
  apply continuousOn_midpointFunctional_positive.mono
  intro z hz
  exact ⟨hz.1, fun i => ⟨(hz.2 i).1, by linarith [(hz.2 i).2]⟩⟩

/-- Positive coin parameters below one give positive sums at every edge, including both ends. -/
theorem edgeSum_pos {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i < 1) (k : Fin (n + 2)) :
    0 < edgeSum p k := by
  have hcount : positiveCoinCount p = n := by simp [positiveCoinCount, hp]
  have hc (j : ℕ) (hj : j ≤ n) : 0 < (bernoulliPolynomial p).coeff j :=
    (coeff_bernoulliPolynomial_pos_iff p (fun i => (hp i).le) hp1 j).mpr (by simpa [hcount])
  have hmass : ∀ j : ℤ, 0 ≤ bernoulliMass p j :=
    bernoulliMass_nonneg p (fun i => (hp i).le) (fun i => (hp1 i).le)
  by_cases hk : k.val ≤ n
  · have hb : 0 < bernoulliMass p (k.val : ℤ) := by
      rw [bernoulliMass_natCast]
      exact hc k.val hk
    exact add_pos_of_nonneg_of_pos (hmass _) hb
  · have hk' : k.val = n + 1 := by omega
    have ha : 0 < bernoulliMass p ((k.val : ℤ) - 1) := by
      rw [show (k.val : ℤ) - 1 = (n : ℤ) by omega, bernoulliMass_natCast]
      exact hc n (le_refl n)
    exact add_pos_of_pos_of_nonneg ha (hmass _)

/-- The concrete coefficient law equals the affine mixture of the background and its shift. -/
theorem bernoulliSum_cons_eq_affineMass {n : ℕ} (p : Fin n → ℝ) (t : ℝ) :
    bernoulliSum (Fin.cons t p) = affineMass
      (fun k : Fin (n + 2) => bernoulliMass p (k.val : ℤ))
      (fun k : Fin (n + 2) => bernoulliMass p ((k.val : ℤ) - 1)) t := by
  funext k
  change (bernoulliPolynomial (Fin.cons t p)).coeff k.val = _
  rw [← bernoulliMass_natCast (Fin.cons t p) k.val, bernoulliMass_cons]
  rfl

theorem affineMass_half_eq_edgeSum {n : ℕ} (p : Fin n → ℝ) (k : Fin (n + 2)) :
    affineMass
      (fun k : Fin (n + 2) => bernoulliMass p (k.val : ℤ))
      (fun k : Fin (n + 2) => bernoulliMass p ((k.val : ℤ) - 1)) (1 / 2) k =
      edgeSum p k / 2 := by
  dsimp [affineMass, edgeSum]
  ring

theorem half_rpow_sub_one (s q : ℝ) (hs : 0 ≤ s) :
    (s / 2) ^ (q - 1) = (2 : ℝ) ^ (1 - q) * s ^ (q - 1) := by
  rw [div_eq_mul_inv, Real.mul_rpow hs (by norm_num), Real.inv_rpow (by norm_num),
    ← Real.rpow_neg (by norm_num), show -(q - 1) = 1 - q by ring]
  ring

/-- Exact fair-target derivative on a positive background support. -/
theorem hasDerivAt_tsallis_cons_half_of_edgeSum_pos {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hq : 0 < q) (hq1 : q ≠ 1) (hs : ∀ k, 0 < edgeSum p k) :
    HasDerivAt (fun t : ℝ => tsallis q (bernoulliSum (Fin.cons t p)))
      (q * (2 : ℝ) ^ (1 - q) * midpointFunctional q p / (1 - q)) (1 / 2) := by
  have hpos (k : Fin (n + 2)) : 0 < affineMass
      (fun k : Fin (n + 2) => bernoulliMass p (k.val : ℤ))
      (fun k : Fin (n + 2) => bernoulliMass p ((k.val : ℤ) - 1)) (1 / 2) k := by
    rw [affineMass_half_eq_edgeSum]
    exact div_pos (hs k) (by norm_num)
  have h := hasDerivAt_tsallis_affine q
    (fun k : Fin (n + 2) => bernoulliMass p (k.val : ℤ))
    (fun k : Fin (n + 2) => bernoulliMass p ((k.val : ℤ) - 1))
    (1 / 2) (ne_of_gt hq) hq1 hpos
  convert h using 1
  · funext t
    rw [bernoulliSum_cons_eq_affineMass]
  · unfold tsallisSlope midpointFunctional edgeDifference
    simp_rw [affineMass_half_eq_edgeSum, half_rpow_sub_one _ q (le_of_lt (hs _))]
    simp_rw [show ∀ k : Fin (n + 2),
      (bernoulliMass p ((k.val : ℤ) - 1) - bernoulliMass p (k.val : ℤ)) *
        ((2 : ℝ) ^ (1 - q) * (edgeSum p k) ^ (q - 1)) =
        (2 : ℝ) ^ (1 - q) *
          ((bernoulliMass p ((k.val : ℤ) - 1) - bernoulliMass p (k.val : ℤ)) *
            (edgeSum p k) ^ (q - 1)) by intro k; ring]
    rw [← Finset.mul_sum]
    ring

/-- Fair-target derivative with positivity derived from the actual half-cube coins. -/
theorem hasDerivAt_tsallis_cons_half {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hq : 0 < q) (hq1 : q ≠ 1) (hp : ∀ i, 0 < p i) (hp1 : ∀ i, p i ≤ 1 / 2) :
    HasDerivAt (fun t : ℝ => tsallis q (bernoulliSum (Fin.cons t p)))
      (q * (2 : ℝ) ^ (1 - q) * midpointFunctional q p / (1 - q)) (1 / 2) :=
  hasDerivAt_tsallis_cons_half_of_edgeSum_pos q p hq hq1
    (edgeSum_pos p hp (fun i => by linarith [hp1 i]))

/-- The same fair-coordinate formula for any named coordinate of an actual coin vector. -/
theorem hasDerivAt_tsallis_update_half {n : ℕ} (q : ℝ)
    (p : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (hq : 0 < q) (hq1 : q ≠ 1)
    (hp : ∀ j, j ≠ i → 0 < p j) (hp1 : ∀ j, j ≠ i → p j ≤ 1 / 2) :
    HasDerivAt (fun t : ℝ => tsallis q (bernoulliSum (Function.update p i t)))
      (q * (2 : ℝ) ^ (1 - q) * midpointFunctional q (omitCoin p i) / (1 - q))
      (1 / 2) := by
  have h := hasDerivAt_tsallis_cons_half q (omitCoin p i) hq hq1
    (fun j => hp (i.succAbove j) (Fin.succAbove_ne i j))
    (fun j => hp1 (i.succAbove j) (Fin.succAbove_ne i j))
  convert h using 1
  funext t
  congr 1
  funext k
  simp only [bernoulliSum, bernoulliPolynomial_update_eq_cons]

/-- Normalization of the background after adding one trailing zero slot. -/
theorem sum_bernoulliMass_padded {n : ℕ} (p : Fin n → ℝ) :
    (∑ k : Fin (n + 2), bernoulliMass p (k.val : ℤ)) = 1 := by
  rw [Fin.sum_univ_castSucc]
  simpa [bernoulliSum] using sum_bernoulliSum p

/-- Normalization of the shifted background, including its zero left slot. -/
theorem sum_shift_bernoulliMass_padded {n : ℕ} (p : Fin n → ℝ) :
    (∑ k : Fin (n + 2), bernoulliMass p ((k.val : ℤ) - 1)) = 1 := by
  rw [Fin.sum_univ_succ]
  simpa [bernoulliSum, Nat.cast_add, Nat.cast_one] using sum_bernoulliSum p

/-- Exact telescoping of all adjacent differences. -/
theorem sum_edgeDifference {n : ℕ} (p : Fin n → ℝ) :
    (∑ k : Fin (n + 2), edgeDifference p k) = 0 := by
  simp only [edgeDifference, Finset.sum_sub_distrib, sum_bernoulliMass_padded,
    sum_shift_bernoulliMass_padded, sub_self]

/-- The unnormalized midpoint functional is identically zero at order one. -/
@[simp] theorem midpointFunctional_one {n : ℕ} (p : Fin n → ℝ) : midpointFunctional 1 p = 0 := by
  simp only [midpointFunctional, sub_self, Real.rpow_zero, mul_one, sum_edgeDifference]

end RenyiMonotonicity
