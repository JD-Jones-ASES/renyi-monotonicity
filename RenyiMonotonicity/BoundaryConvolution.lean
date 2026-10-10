module
public import RenyiMonotonicity.SmallCoinLaw
public import RenyiMonotonicity.BoundaryPair

@[expose] public section
noncomputable section
open scoped BigOperators
open Polynomial

namespace RenyiMonotonicity

/-- A finite coupling estimate from pointwise retention of the old law. -/
theorem probability_sum_abs_sub_le {ι : Type*} [Fintype ι]
    (g h : ι → ℝ) (r : ℝ) (hh : ∀ i, 0 ≤ h i)
    (hgSum : ∑ i, g i = 1) (hhSum : ∑ i, h i = 1)
    (hretain : ∀ i, r * h i ≤ g i) (hr : r ≤ 1) :
    ∑ i, |g i - h i| ≤ 2 * (1 - r) := by
  have hb (i : ι) : |g i - h i| ≤ g i - h i + 2 * (1 - r) * h i := by
    apply abs_le.mpr
    constructor
    · nlinarith [hretain i]
    · nlinarith [mul_nonneg (sub_nonneg.mpr hr) (hh i)]
  calc
    _ ≤ ∑ i, (g i - h i + 2 * (1 - r) * h i) := Finset.sum_le_sum (fun i _ => hb i)
    _ = 2 * (1 - r) := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hgSum, hhSum]
      ring

theorem bernoulliPolynomial_append {m n : ℕ} (p : Fin m → ℝ) (a : Fin n → ℝ) :
    bernoulliPolynomial (Fin.append p a) = bernoulliPolynomial p * bernoulliPolynomial a := by
  simp only [bernoulliPolynomial, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

theorem bernoulliPolynomial_eq_sum_coeff {m : ℕ} (p : Fin m → ℝ) :
    bernoulliPolynomial p = ∑ i : Fin (m + 1), C ((bernoulliPolynomial p).coeff i.val) * X ^ i.val := by
  classical
  ext k
  simp only [finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases hk : k < m + 1
  · let j : Fin (m + 1) := ⟨k, hk⟩
    have he (i : Fin (m + 1)) : k = i.val ↔ i = j := by
      constructor
      · intro h; exact Fin.ext h.symm
      · intro h; subst i; rfl
    simp only [he]
    simp [j]
  · rw [coeff_bernoulliPolynomial_eq_zero p k (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [ite_eq_right (by have := i.isLt; omega)]

/-- The actual coefficient law of appended coins is the finite convolution of
the actual integer-indexed laws, including both support boundaries. -/
theorem bernoulliMass_append {m n : ℕ} (p : Fin m → ℝ) (a : Fin n → ℝ) (k : ℤ) :
    bernoulliMass (Fin.append p a) k =
      ∑ i : Fin (m + 1), bernoulliMass p (i.val : ℤ) * bernoulliMass a (k - i.val) := by
  classical
  by_cases hk : 0 ≤ k
  · lift k to ℕ using hk
    rw [bernoulliMass_natCast, bernoulliPolynomial_append, bernoulliPolynomial_eq_sum_coeff p,
      Finset.sum_mul, finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_assoc, mul_comm (X ^ i.val), coeff_C_mul, coeff_mul_X_pow']
    simp only [bernoulliMass_natCast]
    by_cases hi : i.val ≤ k
    · rw [ite_eq_left hi]
      congr 1
      rw [show (k : ℤ) - i.val = ((k - i.val : ℕ) : ℤ) by omega, bernoulliMass_natCast]
    · rw [ite_eq_right hi, bernoulliMass_neg a _ (by omega), mul_zero]
  · rw [bernoulliMass_neg _ _ (by omega)]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [bernoulliMass_neg a _ (by omega), mul_zero]

theorem bernoulliMass_append_ge_zero_component {m n : ℕ}
    (p : Fin m → ℝ) (a : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) (k : ℤ) :
    bernoulliMass a 0 * bernoulliMass p k ≤ bernoulliMass (Fin.append p a) k := by
  rw [bernoulliMass_append]
  by_cases hk : 0 ≤ k ∧ k ≤ m
  · let j : Fin (m + 1) := ⟨k.toNat, by omega⟩
    have hj : (j.val : ℤ) = k := Int.toNat_of_nonneg hk.1
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun i : Fin (m + 1) => bernoulliMass p (i.val : ℤ) * bernoulliMass a (k - i.val))
      (fun i _ => mul_nonneg (bernoulliMass_nonneg p hp hp1 _) (bernoulliMass_nonneg a ha ha1 _))
      (Finset.mem_univ j)
    simpa only [hj, sub_self, mul_comm] using hh
  · have hz : bernoulliMass p k = 0 := by
      by_cases hk0 : 0 ≤ k
      · simp only [bernoulliMass, ite_eq_left hk0]
        exact coeff_bernoulliPolynomial_eq_zero p k.toNat (by omega)
      · exact bernoulliMass_neg p k (by omega)
    rw [hz, mul_zero]
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (bernoulliMass_nonneg p hp hp1 _) (bernoulliMass_nonneg a ha ha1 _))

/-- The decreasing tail after the old core support is controlled by the odds
of the added coins alone. -/
theorem bernoulliMass_append_tail_odds {m n : ℕ} (p : Fin m → ℝ) (a : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i < 1) (j : ℕ) :
    (j + 1 : ℝ) * bernoulliMass (Fin.append p a) (m + j + 1) ≤
      oddsSum a * bernoulliMass (Fin.append p a) (m + j) := by
  rw [bernoulliMass_append, bernoulliMass_append, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hi : i.val ≤ m := by omega
  have hlow : (j + 1 : ℝ) ≤ (m + j - i.val : ℕ) + 1 := by exact_mod_cast (show j + 1 ≤ m + j - i.val + 1 by omega)
  have hn := coeff_bernoulliPolynomial_nonneg a ha (fun i => (ha1 i).le) (m + j - i.val + 1)
  have hbase := (mul_le_mul_of_nonneg_right hlow hn).trans
    (coeff_bernoulliPolynomial_odds_bound a ha ha1 (m + j - i.val))
  have htail : (j + 1 : ℝ) * bernoulliMass a ((m : ℤ) + j + 1 - i.val) ≤
      oddsSum a * bernoulliMass a ((m : ℤ) + j - i.val) := by
    rw [show (m : ℤ) + j + 1 - i.val = ((m + j - i.val + 1 : ℕ) : ℤ) by omega,
      show (m : ℤ) + j - i.val = ((m + j - i.val : ℕ) : ℤ) by omega]
    simpa only [bernoulliMass_natCast] using hbase
  have hh := mul_le_mul_of_nonneg_left htail (bernoulliMass_nonneg p hp hp1 (i.val : ℤ))
  nlinarith only [hh]

/-- The first new mass retains the last old mass times the one-success event. -/
theorem bernoulliMass_append_first_new_ge {m n : ℕ} (p : Fin m → ℝ) (a : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) :
    bernoulliMass p m * bernoulliMass a 1 ≤ bernoulliMass (Fin.append p a) (m + 1) := by
  rw [bernoulliMass_append]
  have hh := Finset.single_le_sum (s := Finset.univ)
    (f := fun i : Fin (m + 1) => bernoulliMass p (i.val : ℤ) * bernoulliMass a ((m : ℤ) + 1 - i.val))
    (fun i _ => mul_nonneg (bernoulliMass_nonneg p hp hp1 _) (bernoulliMass_nonneg a ha ha1 _))
    (Finset.mem_univ (Fin.last m))
  simpa only [Fin.val_last, add_sub_cancel_left] using hh

theorem sum_bernoulliMass_padding {m N : ℕ} (p : Fin m → ℝ) (hN : m + 1 ≤ N) :
    ∑ k : Fin N, bernoulliMass p (k.val : ℤ) = 1 := by
  induction N, hN using Nat.le_induction with
  | base => simpa only [bernoulliMass_natCast, bernoulliSum] using sum_bernoulliSum p
  | succ N hN ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, bernoulliMass_natCast, coeff_bernoulliPolynomial_eq_zero p N (by omega), add_zero]

/-- The two new adjacent masses together require at least one added success. -/
theorem bernoulliMass_append_first_pair_le {m n : ℕ} (p : Fin m → ℝ) (a : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) :
    bernoulliMass (Fin.append p a) (m + 1) + bernoulliMass (Fin.append p a) (m + 2) ≤ ∑ i, a i := by
  let g := bernoulliMass (Fin.append p a)
  have hg (k : ℤ) : 0 ≤ g k := bernoulliMass_nonneg _
    (by intro i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa only [Fin.append_left] using hp j
        · simpa only [Fin.append_right] using ha j)
    (by intro i; refine Fin.addCases (fun j => ?_) (fun j => ?_) i
        · simpa only [Fin.append_left] using hp1 j
        · simpa only [Fin.append_right] using ha1 j) k
  have htotal : (∑ k : Fin ((m + 1) + (n + 2)), g (k.val : ℤ)) = 1 :=
    sum_bernoulliMass_padding _ (by omega)
  rw [Fin.sum_univ_add] at htotal
  have hcore : bernoulliMass a 0 ≤ ∑ k : Fin (m + 1), g (k.val : ℤ) := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (m + 1))))
      (fun k _ => bernoulliMass_append_ge_zero_component p a hp hp1 ha ha1 (k.val : ℤ))
    rw [← Finset.mul_sum, sum_bernoulliMass_padding p (by omega), mul_one] at hh
    exact hh
  have htail : g (m + 1) + g (m + 2) ≤ ∑ k : Fin (n + 2), g ((m + 1 : ℕ) + k.val) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, Nat.cast_zero, Nat.cast_add, Nat.cast_one, add_zero]
    have hr : 0 ≤ ∑ k : Fin n, g ((m : ℤ) + 1 + (k.val + 1 + 1)) :=
      Finset.sum_nonneg (fun k _ => hg _)
    convert (show g ((m : ℤ) + 1) + g ((m : ℤ) + 1 + 1) ≤
      g ((m : ℤ) + 1) + (g ((m : ℤ) + 1 + 1) + ∑ k : Fin n, g ((m : ℤ) + 1 + (k.val + 1 + 1))) by linarith) using 1 <;>
      congr 1
  simp only [Fin.val_castAdd, Fin.val_natAdd, Nat.cast_add, Nat.cast_one] at htotal
  have hzero : 1 - ∑ i, a i ≤ bernoulliMass a 0 := by
    simpa only [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, bernoulliMass_natCast] using
      coeff_bernoulliPolynomial_zero_ge a ha ha1
  dsimp [g] at htail htotal hcore
  linarith

/-- Total variation control in a common finite padding of the old and new laws. -/
theorem bernoulliMass_append_sum_abs_sub_le {m n N : ℕ} (p : Fin m → ℝ) (a : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (ha : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) (hN : m + n + 1 ≤ N) :
    ∑ k : Fin N, |bernoulliMass (Fin.append p a) (k.val : ℤ) - bernoulliMass p (k.val : ℤ)| ≤
      2 * ∑ i, a i := by
  have hr : bernoulliMass a 0 ≤ 1 := by
    simpa only [bernoulliSum, bernoulliMass, ite_eq_left (show (0 : ℤ) ≤ 0 from le_rfl), Int.toNat_zero, Fin.val_zero] using
      bernoulliSum_le_one a ha ha1 (0 : Fin (n + 1))
  have hh := probability_sum_abs_sub_le
    (fun k : Fin N => bernoulliMass (Fin.append p a) (k.val : ℤ))
    (fun k : Fin N => bernoulliMass p (k.val : ℤ)) (bernoulliMass a 0)
    (fun k => bernoulliMass_nonneg p hp hp1 _)
    (sum_bernoulliMass_padding _ hN) (sum_bernoulliMass_padding p (by omega))
    (fun k => bernoulliMass_append_ge_zero_component p a hp hp1 ha ha1 _) hr
  have hzero : 1 - ∑ i, a i ≤ bernoulliMass a 0 := by
    simpa only [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, bernoulliMass_natCast] using
      coeff_bernoulliPolynomial_zero_ge a ha ha1
  linarith

theorem bernoulliMass_adjacent_le_one {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (k : ℕ) :
    bernoulliMass p k + bernoulliMass p (k + 1) ≤ 1 := by
  classical
  let i : Fin (n + k + 3) := ⟨k, by omega⟩
  let j : Fin (n + k + 3) := ⟨k + 1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; dsimp [i, j] at this; omega
  have hh := Finset.sum_le_sum_of_subset_of_nonneg (s := {i, j}) (t := Finset.univ)
    (f := fun x : Fin (n + k + 3) => bernoulliMass p (x.val : ℤ))
    (Finset.subset_univ _) (fun x _ _ => bernoulliMass_nonneg p hp hp1 _)
  rw [sum_bernoulliMass_padding p (by omega)] at hh
  rw [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by omega, bernoulliMass_natCast, bernoulliMass_natCast]
  simpa [Finset.sum_pair hij, i, j] using hh

theorem edgeSum_le_one {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (k : Fin (n + 2)) :
    edgeSum p k ≤ 1 := by
  by_cases hk : k.val = 0
  · simpa [edgeSum, hk, bernoulliMass, bernoulliSum] using
      bernoulliSum_le_one p hp hp1 (0 : Fin (n + 1))
  · have hh := bernoulliMass_adjacent_le_one p hp hp1 (k.val - 1)
    rw [show ((k.val - 1 : ℕ) : ℤ) = (k.val : ℤ) - 1 by omega,
      show (k.val : ℤ) - 1 + 1 = (k.val : ℤ) by omega] at hh
    exact hh

end RenyiMonotonicity
