module

public import RenyiMonotonicity.BernoulliPolynomial

@[expose] public section

open scoped BigOperators

namespace RenyiMonotonicity

noncomputable def positiveCoinCount {n : ℕ} (p : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => 0 < p i)).card

/-- Product-space probabilities are nonnegative on the entire probability cube. -/
theorem bernoulliWeight_nonneg {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (s : Finset (Fin n)) :
    0 ≤ bernoulliWeight p s := by
  unfold bernoulliWeight
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun i _ => hp i)
  · exact Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (hp1 i))

/-- All coefficient masses are nonnegative, with no strict-positivity assumption. -/
theorem coeff_bernoulliPolynomial_nonneg {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (k : ℕ) :
    0 ≤ (bernoulliPolynomial p).coeff k := by
  rw [coeff_bernoulliPolynomial]
  exact Finset.sum_nonneg (fun s _ => bernoulliWeight_nonneg p hp hp1 s)

theorem bernoulliSum_nonneg {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (k : Fin (n + 1)) :
    0 ≤ bernoulliSum p k := coeff_bernoulliPolynomial_nonneg p hp hp1 k.val

theorem bernoulliSum_le_one {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (k : Fin (n + 1)) :
    bernoulliSum p k ≤ 1 := by
  rw [← sum_bernoulliSum p]
  exact Finset.single_le_sum (fun i _ => bernoulliSum_nonneg p hp hp1 i)
    (Finset.mem_univ k)

/-- If every failure has positive probability, an outcome has positive weight
exactly when all its successful coins have positive probability. -/
theorem bernoulliWeight_pos_iff {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1) (s : Finset (Fin n)) :
    0 < bernoulliWeight p s ↔ ∀ i ∈ s, 0 < p i := by
  constructor
  · intro h i hi
    by_contra hpos
    have hzero : p i = 0 := le_antisymm (le_of_not_gt hpos) (hp i)
    have hz : (∏ j ∈ s, p j) = 0 := Finset.prod_eq_zero hi hzero
    simp [bernoulliWeight, hz] at h
  · intro h
    exact mul_pos (Finset.prod_pos h)
      (Finset.prod_pos (fun i _ => sub_pos.mpr (hp1 i)))

/-- The exact positive support is `0,...,m`, where `m` is the number of positive
coin parameters. The strict upper bound `p < 1` includes every fair coin. -/
theorem coeff_bernoulliPolynomial_pos_iff {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1) (k : ℕ) :
    0 < (bernoulliPolynomial p).coeff k ↔ k ≤ positiveCoinCount p := by
  classical
  rw [coeff_bernoulliPolynomial,
    Finset.sum_pos_iff_of_nonneg (fun s _ =>
      bernoulliWeight_nonneg p hp (fun i => (hp1 i).le) s)]
  constructor
  · rintro ⟨s, hs, hpos⟩
    obtain ⟨_, hk⟩ := Finset.mem_filter.mp hs
    have hsub : s ⊆ Finset.univ.filter (fun i => 0 < p i) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (bernoulliWeight_pos_iff p hp hp1 s).mp hpos i hi⟩
    rw [← hk]
    exact Finset.card_le_card hsub
  · intro hk
    obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hk
    refine ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ s),
      hcard⟩, ?_⟩
    apply (bernoulliWeight_pos_iff p hp hp1 s).mpr
    intro i hi
    exact (Finset.mem_filter.mp (hs hi)).2

theorem positiveCoinCount_le {n : ℕ} (p : Fin n → ℝ) : positiveCoinCount p ≤ n := by
  classical
  simpa [positiveCoinCount] using
    Finset.card_le_card (Finset.filter_subset (fun i => 0 < p i) (Finset.univ : Finset (Fin n)))

theorem bernoulliSum_pos_iff {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1) (k : Fin (n + 1)) :
    0 < bernoulliSum p k ↔ k.val ≤ positiveCoinCount p :=
  coeff_bernoulliPolynomial_pos_iff p hp hp1 k.val

/-- Support has exactly one more point than the number of positive coins,
including the deterministic law with no positive coins. -/
theorem supportCard_bernoulliSum {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1) :
    supportCard (bernoulliSum p) = positiveCoinCount p + 1 := by
  classical
  let m : Fin (n + 1) := ⟨positiveCoinCount p, by have := positiveCoinCount_le p; omega⟩
  have heq : Finset.univ.filter (fun k => 0 < bernoulliSum p k) = Finset.Iic m := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
    exact bernoulliSum_pos_iff p hp hp1 k
  rw [supportCard, heq, Fin.card_Iic]

/-- Order-zero Rényi entropy has the declared support-count meaning. -/
theorem renyi_zero_bernoulliSum {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1) :
    renyi 0 (bernoulliSum p) = Real.log ((positiveCoinCount p : ℝ) + 1) := by
  simp [supportCard_bernoulliSum p hp hp1]

/-- Order-zero Tsallis entropy counts the number of positive coin parameters. -/
theorem tsallis_zero_bernoulliSum {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1) :
    tsallis 0 (bernoulliSum p) = (positiveCoinCount p : ℝ) := by
  simp [supportCard_bernoulliSum p hp hp1]

/-- Increasing parameters cannot remove a positive coin. -/
theorem positiveCoinCount_mono {n : ℕ} (p r : Fin n → ℝ)
    (hpr : ∀ i, p i ≤ r i) : positiveCoinCount p ≤ positiveCoinCount r := by
  classical
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    lt_of_lt_of_le (Finset.mem_filter.mp hi).2 (hpr i)⟩

/-- The complete order-zero Rényi monotonicity theorem on the closed half cube. -/
theorem renyi_zero_monotone {n : ℕ} (p r : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpr : ∀ i, p i ≤ r i) (hr : ∀ i, r i ≤ 1 / 2) :
    renyi 0 (bernoulliSum p) ≤ renyi 0 (bernoulliSum r) := by
  have hp1 : ∀ i, p i < 1 := fun i => lt_of_le_of_lt (hpr i) (by linarith [hr i])
  have hr0 : ∀ i, 0 ≤ r i := fun i => le_trans (hp i) (hpr i)
  have hr1 : ∀ i, r i < 1 := fun i => by linarith [hr i]
  rw [renyi_zero_bernoulliSum p hp hp1, renyi_zero_bernoulliSum r hr0 hr1]
  apply Real.log_le_log (by positivity)
  exact_mod_cast Nat.add_le_add_right (positiveCoinCount_mono p r hpr) 1

/-- The complete order-zero Tsallis monotonicity theorem on the closed half cube. -/
theorem tsallis_zero_monotone {n : ℕ} (p r : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpr : ∀ i, p i ≤ r i) (hr : ∀ i, r i ≤ 1 / 2) :
    tsallis 0 (bernoulliSum p) ≤ tsallis 0 (bernoulliSum r) := by
  have hp1 : ∀ i, p i < 1 := fun i => lt_of_le_of_lt (hpr i) (by linarith [hr i])
  have hr0 : ∀ i, 0 ≤ r i := fun i => le_trans (hp i) (hpr i)
  have hr1 : ∀ i, r i < 1 := fun i => by linarith [hr i]
  rw [tsallis_zero_bernoulliSum p hp hp1, tsallis_zero_bernoulliSum r hr0 hr1]
  exact_mod_cast positiveCoinCount_mono p r hpr

@[simp] theorem shannon_bernoulliSum_empty (p : Fin 0 → ℝ) :
    shannon (bernoulliSum p) = 0 := by simp [shannon]

@[simp] theorem powerSum_bernoulliSum_empty (q : ℝ) (p : Fin 0 → ℝ) :
    powerSum q (bernoulliSum p) = 1 := by simp [powerSum]

@[simp] theorem supportCard_bernoulliSum_empty (p : Fin 0 → ℝ) :
    supportCard (bernoulliSum p) = 1 := by simp [supportCard]

/-- Dimension zero has zero Rényi entropy at every real order. -/
@[simp] theorem renyi_bernoulliSum_empty (q : ℝ) (p : Fin 0 → ℝ) :
    renyi q (bernoulliSum p) = 0 := by simp [renyi]

/-- Dimension zero has zero Tsallis entropy at every real order. -/
@[simp] theorem tsallis_bernoulliSum_empty (q : ℝ) (p : Fin 0 → ℝ) :
    tsallis q (bernoulliSum p) = 0 := by simp [tsallis]

end RenyiMonotonicity
