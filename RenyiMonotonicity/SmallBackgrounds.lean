module
public import RenyiMonotonicity.ResolventRepresentation

@[expose] public section

noncomputable section
open Polynomial Set
open scoped BigOperators

namespace RenyiMonotonicity

theorem four_term_resolvent_identity (A B C z : ℝ)
    (hA : A + z ≠ 0) (hAB : A + B + z ≠ 0)
    (hBC : B + C + z ≠ 0) (hC : C + z ≠ 0) :
    -A / (A + z) + (A - B) / (A + B + z) +
      (B - C) / (B + C + z) + C / (C + z) =
      B * (A - C) * (2 * A * C + z * (A - B + C)) /
        ((A + z) * (A + B + z) * (B + C + z) * (C + z)) := by
  field_simp
  ring

theorem four_term_resolvent_nonneg (A B C z : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hAC : C ≤ A) (hABC : B ≤ A + C) (hz : 0 < z) :
    0 ≤ -A / (A + z) + (A - B) / (A + B + z) +
      (B - C) / (B + C + z) + C / (C + z) := by
  rw [four_term_resolvent_identity A B C z (by positivity) (by positivity)
    (by positivity) (by positivity)]
  apply div_nonneg _ (by positivity)
  apply mul_nonneg (mul_nonneg hB (sub_nonneg.mpr hAC))
  exact add_nonneg (by positivity) (mul_nonneg hz.le (by linarith))

/-- The three-mass analytic base case, with all zero masses allowed. -/
theorem three_mass_midpoint_nonneg {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (A B C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hAC : C ≤ A) (hABC : B ≤ A + C) :
    0 ≤ -A * A ^ (q - 1) + (A - B) * (A + B) ^ (q - 1) +
      (B - C) * (B + C) ^ (q - 1) + C * C ^ (q - 1) := by
  let s : Fin 4 → ℝ := ![A, A + B, B + C, C]
  let d : Fin 4 → ℝ := ![-A, A - B, B - C, C]
  have hs : ∀ i, 0 ≤ s i := by intro i; fin_cases i <;> simp [s] <;> linarith
  have hd : ∀ i, s i = 0 → d i = 0 := by
    intro i
    fin_cases i <;> simp [s, d] <;> intro h <;> linarith
  have hr (t : ℝ) (ht : 0 < t) : 0 ≤ ∑ i, d i / (t + s i) := by
    have hh := four_term_resolvent_nonneg A B C t hA hB hC hAC hABC ht
    simpa [s, d, Fin.sum_univ_succ, add_comm, add_left_comm, add_assoc] using hh
  have hh := power_sum_nonneg_of_resolvent hq s d hs hd hr
  simpa [s, d, Fin.sum_univ_succ, add_assoc] using hh

theorem bernoulliPolynomial_two (p : Fin 2 → ℝ) :
    bernoulliPolynomial p =
      C ((1 - p 0) * (1 - p 1)) +
      C (p 0 * (1 - p 1) + p 1 * (1 - p 0)) * X + C (p 0 * p 1) * X ^ 2 := by
  simp only [bernoulliPolynomial, Fin.prod_univ_two, map_mul, map_add, map_sub, map_one]
  ring

/-- Every two-coin background has a nonnegative actual midpoint functional for
all orders strictly between zero and one, including support-changing faces. -/
theorem midpointFunctional_two_nonneg {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (p : Fin 2 → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1 / 2) :
    0 ≤ midpointFunctional q p := by
  let A := (1 - p 0) * (1 - p 1)
  let B := p 0 * (1 - p 1) + p 1 * (1 - p 0)
  let C := p 0 * p 1
  have hA : 0 ≤ A := mul_nonneg (by linarith [hp1 0]) (by linarith [hp1 1])
  have hB : 0 ≤ B := add_nonneg
    (mul_nonneg (hp 0) (by linarith [hp1 1])) (mul_nonneg (hp 1) (by linarith [hp1 0]))
  have hC : 0 ≤ C := mul_nonneg (hp 0) (hp 1)
  have hAC : C ≤ A := by dsimp [A, C]; nlinarith [hp1 0, hp1 1]
  have hABC : B ≤ A + C := by
    have hh := mul_nonneg (show 0 ≤ 1 - 2 * p 0 by linarith [hp1 0])
      (show 0 ≤ 1 - 2 * p 1 by linarith [hp1 1])
    dsimp [A, B, C]
    nlinarith
  have hh := three_mass_midpoint_nonneg hq A B C hA hB hC hAC hABC
  have hpoly : bernoulliPolynomial p = Polynomial.C A + Polynomial.C B * X +
      Polynomial.C C * X ^ 2 := bernoulliPolynomial_two p
  have hm0 : bernoulliMass p 0 = A := by norm_num [bernoulliMass, hpoly]
  have hm1 : bernoulliMass p 1 = B := by norm_num [bernoulliMass, hpoly, coeff_C_mul]
  have hm2 : bernoulliMass p 2 = C := by norm_num [bernoulliMass, hpoly, coeff_C_mul]
  have hm3 : bernoulliMass p 3 = 0 := by norm_num [bernoulliMass, hpoly, coeff_C_mul]
  have hmn : bernoulliMass p (-1) = 0 := by simp [bernoulliMass]
  convert hh using 1
  norm_num [midpointFunctional, edgeDifference, edgeSum, Fin.sum_univ_succ,
    hm0, hm1, hm2, hm3, hmn, hpoly, coeff_C_mul, coeff_X, add_assoc]

/-- Adding a zero coin only appends a zero adjacent pair. -/
@[simp] theorem midpointFunctional_cons_zero {n : ℕ} (q : ℝ) (p : Fin n → ℝ) :
    midpointFunctional q (Fin.cons 0 p) = midpointFunctional q p := by
  have hm1 : bernoulliMass p ((n + 1 : ℕ) : ℤ) = 0 := by
    rw [bernoulliMass_natCast]
    exact coeff_bernoulliPolynomial_eq_zero p _ (by omega)
  have hm2 : bernoulliMass p ((n + 2 : ℕ) : ℤ) = 0 := by
    rw [bernoulliMass_natCast]
    exact coeff_bernoulliPolynomial_eq_zero p _ (by omega)
  unfold midpointFunctional
  rw [Fin.sum_univ_castSucc]
  simp only [edgeDifference, edgeSum, bernoulliMass_cons_zero, Fin.val_castSucc,
    Fin.val_last]
  rw [show ((n + 2 : ℕ) : ℤ) - 1 = ((n + 1 : ℕ) : ℤ) by omega, hm1, hm2]
  simp

theorem midpointFunctional_one_coin_nonneg {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (p : Fin 1 → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1 / 2) :
    0 ≤ midpointFunctional q p := by
  have h := midpointFunctional_two_nonneg hq (Fin.cons 0 p)
    (by intro i; fin_cases i <;> simp [hp])
    (by
      intro i
      fin_cases i
      · norm_num
      · simpa using hp1 0)
  simpa using h

theorem midpointFunctional_empty_nonneg {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (p : Fin 0 → ℝ) : 0 ≤ midpointFunctional q p := by
  have h := midpointFunctional_one_coin_nonneg hq (Fin.cons 0 p)
    (by intro i; fin_cases i; simp)
    (by intro i; fin_cases i; norm_num)
  simpa using h

/-- The analytic base case excludes every background of at most two coins. -/
theorem midpointFunctional_small_nonneg {n : ℕ} (hn : n ≤ 2)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1 / 2) :
    0 ≤ midpointFunctional q p := by
  interval_cases n
  · exact midpointFunctional_empty_nonneg hq p
  · exact midpointFunctional_one_coin_nonneg hq p hp hp1
  · exact midpointFunctional_two_nonneg hq p hp hp1

theorem three_le_of_midpointFunctional_neg {n : ℕ} {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1)
    (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1 / 2)
    (hneg : midpointFunctional q p < 0) : 3 ≤ n := by
  by_contra hn
  have h := midpointFunctional_small_nonneg (show n ≤ 2 by omega) hq p hp hp1
  linarith

end RenyiMonotonicity
