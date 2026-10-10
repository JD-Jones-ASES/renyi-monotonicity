module

public import RenyiMonotonicity.HarmonicGap
public import RenyiMonotonicity.HarmonicKernelSeries

@[expose] public section

namespace RenyiMonotonicity

/-- One point of the shortened mixing grid. -/
noncomputable def loweredMixingPoint (A gap : ℝ) : ℝ := A / (1 - gap)

/-- The new grid comes from the actual lowered adjacent masses by cancellation
of the common positive old mass. -/
theorem loweredMixingPoint_mass_identity (g A B : ℝ) (hg : g ≠ 0) :
    (g * A) / (g * A + g * (1 - B)) = loweredMixingPoint A (B - A) := by
  rw [show g * A + g * (1 - B) = g * (1 - (B - A)) by ring]
  exact mul_div_mul_left A (1 - (B - A)) hg

/-- Strict increase of consecutive lowered mixing points, including boundary points. -/
theorem loweredMixingPoint_lt (A a b : ℝ) (hA : 0 ≤ A)
    (ha : 0 < a) (hb : 0 < b) (htotal : A + a + b ≤ 1) :
    loweredMixingPoint A a < loweredMixingPoint (A + a) b := by
  have ha1 : a < 1 := by linarith
  have hb1 : b < 1 := by linarith
  unfold loweredMixingPoint
  rw [div_lt_div_iff₀ (sub_pos.mpr ha1) (sub_pos.mpr hb1)]
  have hpos : 0 < a * (1 - A - a) := mul_pos ha (by linarith)
  have hnonneg : 0 ≤ A * b := mul_nonneg hA hb.le
  nlinarith

/-- A positive affine combination of the two endpoint checks proves concavity
of the lowered grid for every admissible old grid. -/
theorem loweredMixingPoint_concave (A a b c : ℝ)
    (hc : 0 < c) (hcb : c ≤ b) (hba : b ≤ a)
    (hA : 0 ≤ A) (hbound : A ≤ 1 - a - b - c) :
    loweredMixingPoint (A + a + b) c - loweredMixingPoint (A + a) b ≤
      loweredMixingPoint (A + a) b - loweredMixingPoint A a := by
  have ha : 0 < a := lt_of_lt_of_le (lt_of_lt_of_le hc hcb) hba
  have hb : 0 < b := lt_of_lt_of_le hc hcb
  have ha1 : a < 1 := by linarith
  have hb1 : b < 1 := by linarith
  have hc1 : c < 1 := by linarith
  have hda : 0 < 1 - a := sub_pos.mpr ha1
  have hdb : 0 < 1 - b := sub_pos.mpr hb1
  have hdc : 0 < 1 - c := sub_pos.mpr hc1
  let L : ℝ := 1 - a - b - c
  let E : ℝ → ℝ := fun t => 2 * (t + a) / (1 - b) - t / (1 - a) - (t + a + b) / (1 - c)
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have h0 : E 0 = ((a - b) * (1 - b) + 2 * a * (b - c)) / ((1 - b) * (1 - c)) := by
    dsimp [E]
    field_simp
    ring
  have hLval : E L = ((b - c) * (1 - b) + 2 * c * (a - b)) / ((1 - a) * (1 - b)) := by
    dsimp [E, L]
    field_simp
    ring
  have he0 : 0 ≤ E 0 := by
    rw [h0]
    exact div_nonneg
      (add_nonneg (mul_nonneg (sub_nonneg.mpr hba) hdb.le)
        (mul_nonneg (mul_nonneg (by norm_num) ha.le) (sub_nonneg.mpr hcb)))
      (mul_pos hdb hdc).le
  have heL : 0 ≤ E L := by
    rw [hLval]
    exact div_nonneg
      (add_nonneg (mul_nonneg (sub_nonneg.mpr hcb) hdb.le)
        (mul_nonneg (mul_nonneg (by norm_num) hc.le) (sub_nonneg.mpr hba)))
      (mul_pos hda hdb).le
  have heA : 0 ≤ E A := by
    rcases eq_or_lt_of_le hL with hzero | hpos
    · have hAz : A = 0 := by dsimp [L] at hzero; linarith
      simpa [hAz] using he0
    · have hid : L * E A = (L - A) * E 0 + A * E L := by dsimp [E]; ring
      have hprod : 0 ≤ L * E A := by
        rw [hid]
        exact add_nonneg (mul_nonneg (sub_nonneg.mpr hbound) he0) (mul_nonneg hA heL)
      nlinarith
  dsimp [E] at heA
  rw [mul_div_assoc] at heA
  dsimp [loweredMixingPoint]
  linarith

/-- A positive finite mass sequence of length `n+1`, with its balanced, strictly
increasing, concave mixing grid. Only the displayed bounded indices are used. -/
structure HarmonicSequence (n : ℕ) where
  mass : ℕ → ℝ
  node : ℕ → ℝ
  mass_pos : ∀ k, k ≤ n → 0 < mass k
  node_zero : node 0 = 0
  node_last : node (n + 1) = 1
  node_step : ∀ k, k ≤ n → node k < node (k + 1)
  concave : ∀ k, k < n → node (k + 2) - node (k + 1) ≤ node (k + 1) - node k
  balance : ∀ k, k < n → mass k * (1 - node (k + 1)) = mass (k + 1) * node (k + 1)

namespace HarmonicSequence

variable {n : ℕ}

def gap (s : HarmonicSequence n) (k : ℕ) : ℝ := s.node (k + 1) - s.node k

theorem node_mono (s : HarmonicSequence n) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n + 1) :
    s.node i ≤ s.node j := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    exact (ih (by omega)).trans (s.node_step j (by omega)).le

theorem node_strict (s : HarmonicSequence n) {i j : ℕ} (hij : i < j) (hj : j ≤ n + 1) :
    s.node i < s.node j :=
  (s.node_step i (by omega)).trans_le (s.node_mono (by omega) hj)

theorem node_nonneg (s : HarmonicSequence n) {k : ℕ} (hk : k ≤ n + 1) : 0 ≤ s.node k := by
  simpa [s.node_zero] using s.node_mono (Nat.zero_le k) hk

theorem node_le_one (s : HarmonicSequence n) {k : ℕ} (hk : k ≤ n + 1) : s.node k ≤ 1 := by
  simpa [s.node_last] using s.node_mono hk (le_refl (n + 1))

theorem node_lt_one (s : HarmonicSequence n) {k : ℕ} (hk : k ≤ n) : s.node k < 1 := by
  simpa [s.node_last] using s.node_strict (show k < n + 1 by omega) (le_refl (n + 1))

theorem node_pos (s : HarmonicSequence n) {k : ℕ} (hk0 : 0 < k) (hk : k ≤ n + 1) :
    0 < s.node k := by
  simpa [s.node_zero] using s.node_strict hk0 hk

theorem gap_pos (s : HarmonicSequence n) {k : ℕ} (hk : k ≤ n) : 0 < s.gap k :=
  sub_pos.mpr (s.node_step k hk)

theorem gap_antitone (s : HarmonicSequence n) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ n) :
    s.gap j ≤ s.gap i := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    exact (s.concave j (by omega)).trans (ih (by omega))

theorem gap_lt_one (s : HarmonicSequence (n + 1)) {k : ℕ} (hk : k ≤ n + 1) :
    s.gap k < 1 := by
  by_cases hk0 : k = 0
  · subst k
    simpa [gap, s.node_zero] using s.node_lt_one (show 1 ≤ n + 1 by omega)
  · have ha := s.node_pos (Nat.pos_of_ne_zero hk0) (show k ≤ n + 1 + 1 by omega)
    have hb := s.node_le_one (show k + 1 ≤ n + 1 + 1 by omega)
    dsimp [gap]
    linarith

/-- Shorten a positive balanced sequence by one mass. The lowered grid is proved
strictly increasing and concave from the old grid, rather than assumed. -/
noncomputable def lower (s : HarmonicSequence (n + 1)) : HarmonicSequence n where
  mass k := s.mass k * (1 - s.node (k + 1))
  node k := loweredMixingPoint (s.node k) (s.gap k)
  mass_pos k hk := mul_pos (s.mass_pos k (by omega))
    (sub_pos.mpr (s.node_lt_one (by omega)))
  node_zero := by simp [loweredMixingPoint, s.node_zero]
  node_last := by
    have hpos := s.node_pos (show 0 < n + 1 by omega) (show n + 1 ≤ n + 1 + 1 by omega)
    simp only [loweredMixingPoint, gap, s.node_last]
    rw [show 1 - (1 - s.node (n + 1)) = s.node (n + 1) by ring]
    exact div_self (ne_of_gt hpos)
  node_step k hk := by
    have h := loweredMixingPoint_lt (s.node k) (s.gap k) (s.gap (k + 1))
      (s.node_nonneg (by omega)) (s.gap_pos (by omega)) (s.gap_pos (by omega))
    have hb := s.node_le_one (show k + 2 ≤ n + 1 + 1 by omega)
    have ht : s.node k + s.gap k + s.gap (k + 1) ≤ 1 := by
      dsimp [gap]
      simpa only [Nat.add_assoc] using (by linarith :
        s.node k + (s.node (k + 1) - s.node k) + (s.node (k + 2) - s.node (k + 1)) ≤ 1)
    simpa only [gap, show s.node k + (s.node (k + 1) - s.node k) = s.node (k + 1) by ring]
      using h ht
  concave k hk := by
    have h := loweredMixingPoint_concave (s.node k) (s.gap k) (s.gap (k + 1)) (s.gap (k + 2))
      (s.gap_pos (by omega)) (s.concave (k + 1) (by omega)) (s.concave k (by omega))
      (s.node_nonneg (by omega))
    have hb := s.node_le_one (show k + 3 ≤ n + 1 + 1 by omega)
    have hbound : s.node k ≤ 1 - s.gap k - s.gap (k + 1) - s.gap (k + 2) := by
      dsimp [gap]
      simp only [show k + 1 + 1 = k + 2 by omega, show k + 2 + 1 = k + 3 by omega]
      linarith
    convert h hbound using 1 <;> dsimp [gap] <;> congr 2 <;> ring
  balance k hk := by
    have hd := ne_of_gt (sub_pos.mpr (s.gap_lt_one (show k + 1 ≤ n + 1 by omega)))
    have hb := s.balance k (by omega)
    dsimp [loweredMixingPoint]
    rw [hb]
    field_simp
    dsimp [gap]
    ring

@[simp] theorem lower_mass (s : HarmonicSequence (n + 1)) (k : ℕ) :
    s.lower.mass k = s.mass k * (1 - s.node (k + 1)) := rfl

@[simp] theorem lower_node (s : HarmonicSequence (n + 1)) (k : ℕ) :
    s.lower.node k = s.node k / (1 - s.gap k) := rfl

/-- Centered grid location. -/
noncomputable def center (s : HarmonicSequence n) (k : ℕ) : ℝ := s.node k - 1 / 2

theorem abs_center_le (s : HarmonicSequence n) {k : ℕ} (hk : k ≤ n + 1) :
    |s.center k| ≤ 1 / 2 := by
  rw [abs_le]
  have ha := s.node_nonneg hk
  have hb := s.node_le_one hk
  dsimp [center]
  constructor <;> linarith

/-- Weighted increments over the finite mixing grid. -/
noncomputable def functional (s : HarmonicSequence n) (q : ℝ) (F : ℝ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), s.mass k ^ q * (F (s.center (k + 1)) - F (s.center k))

/-- Every even moment includes the constant moment, which is identically zero. -/
noncomputable def moment (s : HarmonicSequence n) (q : ℝ) (m : ℕ) : ℝ :=
  s.functional q (fun x => x ^ (2 * m))

@[simp] theorem moment_zero (s : HarmonicSequence n) (q : ℝ) : s.moment q 0 = 0 := by
  simp [moment, functional]

@[simp] theorem moment_singleton (s : HarmonicSequence 0) (q : ℝ) (m : ℕ) :
    s.moment q m = 0 := by
  simp only [moment, functional, Nat.zero_add, Finset.sum_range_one, center,
    s.node_zero, s.node_last]
  rw [show (0 : ℝ) - 1 / 2 = -(1 - 1 / 2) by ring, Even.neg_pow (even_two_mul m)]
  ring

/-- Coefficients of the lowered summation-by-parts identity. -/
noncomputable def lowerFlux (s : HarmonicSequence (n + 1)) (q : ℝ) (k : ℕ) : ℝ :=
  (s.mass k * s.node k) ^ q - (s.mass k * (1 - s.node (k + 1))) ^ q

/-- Exact finite summation by parts, with both outer zero masses derived from
endpoints of the old mixing grid. -/
theorem sum_lowerFlux (s : HarmonicSequence (n + 1)) (q : ℝ) (hq : 0 < q) (F : ℝ → ℝ) :
    (∑ k ∈ Finset.range (n + 2), s.lowerFlux q k * F (s.lower.center k)) =
      s.lower.functional q F := by
  simp only [lowerFlux, sub_mul, Finset.sum_sub_distrib]
  have hl : (∑ k ∈ Finset.range (n + 2), (s.mass k * s.node k) ^ q * F (s.lower.center k)) =
      ∑ k ∈ Finset.range (n + 1), s.lower.mass k ^ q * F (s.lower.center (k + 1)) := by
    rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ']
    simp only [s.node_zero, mul_zero, Real.zero_rpow (ne_of_gt hq), zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    rw [lower_mass, s.balance k (by simpa only [Finset.mem_range] using hk)]
  have hr : (∑ k ∈ Finset.range (n + 2), (s.mass k * (1 - s.node (k + 1))) ^ q * F (s.lower.center k)) =
      ∑ k ∈ Finset.range (n + 1), s.lower.mass k ^ q * F (s.lower.center k) := by
    rw [show n + 2 = (n + 1) + 1 by omega, Finset.sum_range_succ]
    simp only [s.node_last, sub_self, mul_zero, Real.zero_rpow (ne_of_gt hq), zero_mul, add_zero]
    rfl
  rw [hl, hr, ← Finset.sum_sub_distrib]
  simp only [functional, mul_sub]

/-- The left and right old interval endpoints in terms of the centered new grid. -/
theorem lower_endpoint_identities (s : HarmonicSequence (n + 1)) {k : ℕ} (hk : k ≤ n + 1) :
    (1 - s.gap k) * s.lower.center k - s.gap k / 2 = s.center k ∧
    (1 - s.gap k) * s.lower.center k + s.gap k / 2 = s.center (k + 1) := by
  have hd : 1 - s.gap k ≠ 0 := ne_of_gt (sub_pos.mpr (s.gap_lt_one hk))
  dsimp [center]
  constructor <;> field_simp <;> dsimp [gap] <;> ring

/-- The sign of a lowered flux agrees with the centered lowered node. -/
theorem lowerFlux_nonpos (s : HarmonicSequence (n + 1)) (q : ℝ) (hq : 0 ≤ q)
    {k : ℕ} (hk : k ≤ n + 1) (hx : s.lower.center k ≤ 0) : s.lowerFlux q k ≤ 0 := by
  have hg := s.mass_pos k hk
  have ha := s.node_nonneg (show k ≤ n + 1 + 1 by omega)
  have hb := s.node_le_one (show k + 1 ≤ n + 1 + 1 by omega)
  have hd := sub_pos.mpr (s.gap_lt_one hk)
  have hdiv : s.node k / (1 - s.gap k) ≤ 1 / 2 := by
    simpa only [center, lower_node, sub_nonpos] using hx
  have hab : s.node k ≤ 1 - s.node (k + 1) := by
    rw [div_le_iff₀ hd] at hdiv
    dsimp [gap] at hdiv
    linarith
  exact sub_nonpos.mpr (Real.rpow_le_rpow (mul_nonneg hg.le ha)
    (mul_le_mul_of_nonneg_left hab hg.le) hq)

theorem lowerFlux_nonneg (s : HarmonicSequence (n + 1)) (q : ℝ) (hq : 0 ≤ q)
    {k : ℕ} (hk : k ≤ n + 1) (hx : 0 ≤ s.lower.center k) : 0 ≤ s.lowerFlux q k := by
  have hg := s.mass_pos k hk
  have ha := s.node_nonneg (show k ≤ n + 1 + 1 by omega)
  have hb := s.node_le_one (show k + 1 ≤ n + 1 + 1 by omega)
  have hd := sub_pos.mpr (s.gap_lt_one hk)
  have hdiv : 1 / 2 ≤ s.node k / (1 - s.gap k) := by
    simpa only [center, lower_node, sub_nonneg] using hx
  have hab : 1 - s.node (k + 1) ≤ s.node k := by
    rw [le_div_iff₀ hd] at hdiv
    dsimp [gap] at hdiv
    linarith
  exact sub_nonneg.mpr (Real.rpow_le_rpow (mul_nonneg hg.le (sub_nonneg.mpr hb))
    (mul_le_mul_of_nonneg_left hab hg.le) hq)

theorem lowerFlux_eq (s : HarmonicSequence (n + 1)) (q : ℝ)
    {k : ℕ} (hk : k ≤ n + 1) :
    s.lowerFlux q k = s.mass k ^ q * (1 - s.gap k) ^ q *
      harmonicOddDenominator q (s.lower.center k) := by
  have hg := s.mass_pos k hk
  have hd := sub_pos.mpr (s.gap_lt_one hk)
  have hx := s.lower.abs_center_le (show k ≤ n + 1 by omega)
  have hplus : 0 ≤ 1 / 2 + s.lower.center k := by have := (abs_le.mp hx).1; linarith
  have hminus : 0 ≤ 1 / 2 - s.lower.center k := by have := (abs_le.mp hx).2; linarith
  have hA : s.node k = (1 - s.gap k) * (1 / 2 + s.lower.center k) := by
    dsimp [center]
    field_simp
    ring
  have hB : 1 - s.node (k + 1) = (1 - s.gap k) * (1 / 2 - s.lower.center k) := by
    dsimp [center]
    field_simp
    dsimp [gap]
    ring
  simp only [lowerFlux, hA, hB, Real.mul_rpow hg.le (mul_nonneg hd.le hplus),
    Real.mul_rpow hg.le (mul_nonneg hd.le hminus), Real.mul_rpow hd.le hplus,
    Real.mul_rpow hd.le hminus, harmonicOddDenominator]
  ring

/-- The exact identity of an old moment with the variable-gap lowered kernel. -/
theorem moment_eq_lowerFlux (s : HarmonicSequence (n + 1)) (q : ℝ) (hq : 0 < q) (m : ℕ) :
    s.moment q m = ∑ k ∈ Finset.range (n + 2), s.lowerFlux q k *
      harmonicLoweringKernel (2 * m) q (s.gap k) (s.lower.center k) := by
  unfold moment functional
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n + 1 := by simp only [Finset.mem_range] at hk; omega
  have he := s.lower_endpoint_identities hk'
  rw [← he.1, ← he.2, s.lowerFlux_eq q hk']
  by_cases hx0 : s.lower.center k = 0
  · simp only [hx0, mul_zero, zero_sub, zero_add, harmonicOddDenominator, add_zero,
      sub_zero, sub_self, mul_zero, Even.neg_pow (even_two_mul m), zero_mul]
  · have hx := s.lower.abs_center_le (show k ≤ n + 1 by omega)
    have hden : harmonicOddDenominator q (s.lower.center k) ≠ 0 := by
      rcases lt_or_gt_of_ne hx0 with hneg | hpos
      · have hp := harmonicOddDenominator_pos q (-s.lower.center k) hq (neg_pos.mpr hneg)
          (by simpa [abs_of_neg hneg] using hx)
        have heq : harmonicOddDenominator q (-s.lower.center k) =
            -harmonicOddDenominator q (s.lower.center k) := by
          unfold harmonicOddDenominator
          simp only [← sub_eq_add_neg, sub_neg_eq_add]
          ring
        rw [heq] at hp
        exact ne_of_lt (by linarith)
      · exact ne_of_gt (harmonicOddDenominator_pos q (s.lower.center k) hq hpos
          (by simpa [abs_of_pos hpos] using hx))
    have hpow : (1 - s.gap k) ^ q ≠ 0 := ne_of_gt
      (Real.rpow_pos_of_pos (sub_pos.mpr (s.gap_lt_one hk')) q)
    simp only [harmonicLoweringKernel, hx0, ↓reduceIte, harmonicLoweringQuotient]
    field_simp

/-- A common gap can be chosen at the first nonnegative centered node. No
coefficientwise monotonicity of a power series is used. -/
theorem exists_common_gap (s : HarmonicSequence (n + 1)) (q : ℝ) (hq : 1 ≤ q)
    (m : ℕ) (hm : 0 < m) :
    ∃ δ ∈ Set.Ioo (0 : ℝ) 1, s.moment q m ≤
      s.lower.functional q (harmonicLoweringKernel (2 * m) q δ) := by
  classical
  have hex : ∃ k : ℕ, k ≤ n + 1 ∧ 0 ≤ s.lower.center k := by
    refine ⟨n + 1, le_refl _, ?_⟩
    simp only [center, s.lower.node_last]
    norm_num
  let t := Nat.find hex
  have ht : t ≤ n + 1 ∧ 0 ≤ s.lower.center t := Nat.find_spec hex
  refine ⟨s.gap t, ⟨s.gap_pos ht.1, s.gap_lt_one ht.1⟩, ?_⟩
  rw [s.moment_eq_lowerFlux q (by linarith) m, ← s.sum_lowerFlux q (by linarith)]
  apply Finset.sum_le_sum
  intro k hk
  have hk' : k ≤ n + 1 := by simp only [Finset.mem_range] at hk; omega
  have hkδ : s.gap k ∈ Set.Ioo (0 : ℝ) 1 := ⟨s.gap_pos hk', s.gap_lt_one hk'⟩
  have htδ : s.gap t ∈ Set.Ioo (0 : ℝ) 1 := ⟨s.gap_pos ht.1, s.gap_lt_one ht.1⟩
  have hmono := harmonicLoweringKernel_monotoneOn (2 * m) (even_two_mul m) (by omega)
    q (s.lower.center k) hq (s.lower.abs_center_le hk')
  by_cases hkt : k < t
  · have hx : s.lower.center k < 0 := by
      by_contra hneg
      have hmin := Nat.find_min' hex ⟨hk', le_of_not_gt hneg⟩
      change t ≤ k at hmin
      omega
    exact mul_le_mul_of_nonpos_left
      (hmono htδ hkδ (s.gap_antitone hkt.le ht.1))
      (s.lowerFlux_nonpos q (by linarith) hk' hx.le)
  · have htk : t ≤ k := Nat.le_of_not_gt hkt
    have hx : 0 ≤ s.lower.center k := by
      have hnode := s.lower.node_mono htk hk'
      have htcenter := ht.2
      change 0 ≤ s.lower.node t - 1 / 2 at htcenter
      change 0 ≤ s.lower.node k - 1 / 2
      linarith
    exact mul_le_mul_of_nonneg_left
      (hmono hkδ htδ (s.gap_antitone htk hk'))
      (s.lowerFlux_nonneg q (by linarith) hk' hx)

/-- Finite weighted increments commute with a convergent nonnegative even
series, including the two boundary nodes. This uses actual `HasSum` convergence. -/
theorem functional_nonpos_of_evenSeries {ι : Type*} (s : HarmonicSequence n) (q : ℝ)
    (F : ℝ → ℝ) (c : ι → ℝ) (degree : ι → ℕ)
    (hc : ∀ i, 0 ≤ c i)
    (hseries : ∀ x : ℝ, |x| ≤ 1 / 2 → HasSum (fun i => c i * x ^ (2 * degree i)) (F x))
    (hmoment : ∀ m : ℕ, s.moment q m ≤ 0) : s.functional q F ≤ 0 := by
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
  exact hasSum_le (fun i => mul_nonpos_of_nonneg_of_nonpos (hc i) (hmoment (degree i)))
    hs hasSum_zero

/-- Harmonic lowering for every finite positive balanced concave grid, all even
moments simultaneously, and every real order in the closed interval `[1,2]`.
The induction shortens the actual mass sequence and uses convergent positive
series of the actual lowering kernel. -/
theorem moment_nonpos (q : ℝ) (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2) :
    ∀ {n : ℕ} (s : HarmonicSequence n) (m : ℕ), s.moment q m ≤ 0 := by
  intro n
  induction n with
  | zero => intro s m; simp
  | succ n ih =>
    intro s m
    by_cases hm : m = 0
    · subst m; simp
    obtain ⟨δ, hδ, hstep⟩ := s.exists_common_gap q hq₁ m (Nat.pos_of_ne_zero hm)
    apply hstep.trans
    exact s.lower.functional_nonpos_of_evenSeries q
      (harmonicLoweringKernel (2 * m) q δ) (harmonicLoweringSeriesCoefficient m q δ)
      harmonicLoweringSeriesDegree
      (harmonicLoweringSeriesCoefficient_nonneg m q δ hq₁ hq₂ hδ.1 hδ.2)
      (hasSum_harmonicLoweringKernel m q δ hq₁ hq₂) (ih s.lower)

/-- The harmonic even kernel itself inherits the sign from all even moments. -/
theorem functional_harmonicEvenKernel_nonpos (s : HarmonicSequence n) (q : ℝ)
    (hq₁ : 1 ≤ q) (hq₂ : q ≤ 2) : s.functional q (harmonicEvenKernel q) ≤ 0 :=
  s.functional_nonpos_of_evenSeries q (harmonicEvenKernel q)
    (harmonicEvenSeriesCoefficient q) (fun w => positiveWordDegree w.1 w.2)
    (harmonicEvenSeriesCoefficient_nonneg q hq₁ hq₂)
    (hasSum_harmonicEvenKernel q hq₁ hq₂) (moment_nonpos q hq₁ hq₂ s)

end HarmonicSequence

end RenyiMonotonicity
