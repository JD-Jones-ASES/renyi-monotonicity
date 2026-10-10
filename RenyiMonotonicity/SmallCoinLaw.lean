module
public import RenyiMonotonicity.CubicIdentities

@[expose] public section
noncomputable section
open scoped BigOperators
open Polynomial

namespace RenyiMonotonicity

def oddsSum {n : ℕ} (p : Fin n → ℝ) : ℝ := ∑ i, p i / (1 - p i)

theorem coeff_bernoulliPolynomial_zero {n : ℕ} (p : Fin n → ℝ) :
    (bernoulliPolynomial p).coeff 0 = ∏ i, (1 - p i) := by
  rw [coeff_zero_eq_eval_zero]
  simp only [bernoulliPolynomial, eval_prod, eval_add, eval_C, eval_mul, eval_X,
    mul_zero, add_zero]

theorem coeff_bernoulliPolynomial_zero_ge {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    1 - ∑ i, p i ≤ (bernoulliPolynomial p).coeff 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have htail := ih (fun i => p i.succ) (fun i => hp i.succ) (fun i => hp1 i.succ)
    have hs : 0 ≤ ∑ i : Fin n, p i.succ := Finset.sum_nonneg (fun i _ => hp _)
    have hprod : (bernoulliPolynomial p).coeff 0 =
        (1 - p 0) * (bernoulliPolynomial (fun i : Fin n => p i.succ)).coeff 0 := by
      simp only [coeff_bernoulliPolynomial_zero, Fin.prod_univ_succ]
    rw [hprod, Fin.sum_univ_succ]
    nlinarith [mul_nonneg (sub_nonneg.mpr (hp1 0))
      (sub_nonneg.mpr htail), mul_nonneg (hp 0) hs]

theorem coeff_bernoulliPolynomial_derivative {n : ℕ} (p : Fin (n + 1) → ℝ) (k : ℕ) :
    (k + 1 : ℝ) * (bernoulliPolynomial p).coeff (k + 1) =
      ∑ i, p i * (bernoulliPolynomial (omitCoin p i)).coeff k := by
  have h := congrArg (fun P : Polynomial ℝ => P.coeff k) (derivative_bernoulliPolynomial p)
  simp only [coeff_derivative, finsetSum_coeff, coeff_C_mul] at h
  simpa only [mul_comm] using h

theorem coeff_bernoulliPolynomial_omit_le {n : ℕ} (p : Fin (n + 1) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (i : Fin (n + 1)) (k : ℕ) :
    (1 - p i) * (bernoulliPolynomial (omitCoin p i)).coeff k ≤
      (bernoulliPolynomial p).coeff k := by
  have he : bernoulliPolynomial p = bernoulliPolynomial (Fin.cons (p i) (omitCoin p i)) := by
    rw [bernoulliPolynomial_omit p i, bernoulliPolynomial_cons]
  rw [he]
  cases k with
  | zero => rw [coeff_bernoulliPolynomial_cons_zero]
  | succ k =>
    rw [coeff_bernoulliPolynomial_cons_succ]
    exact le_add_of_nonneg_right (mul_nonneg (hp i)
      (coeff_bernoulliPolynomial_nonneg _ (fun j => hp _) (fun j => hp1 _) _))

/-- The elementary-symmetric counting bound for every coefficient, including
zero coefficients outside the support. -/
theorem coeff_bernoulliPolynomial_odds_bound {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1) (k : ℕ) :
    (k + 1 : ℝ) * (bernoulliPolynomial p).coeff (k + 1) ≤
      oddsSum p * (bernoulliPolynomial p).coeff k := by
  cases n with
  | zero => simp [oddsSum, bernoulliPolynomial_empty, coeff_one]
  | succ n =>
    rw [coeff_bernoulliPolynomial_derivative, oddsSum, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hi : 0 < 1 - p i := sub_pos.mpr (hp1 i)
    have h := mul_le_mul_of_nonneg_left
      (coeff_bernoulliPolynomial_omit_le p hp (fun j => (hp1 j).le) i k)
      (div_nonneg (hp i) hi.le)
    calc
      _ = (p i / (1 - p i)) * ((1 - p i) * (bernoulliPolynomial (omitCoin p i)).coeff k) := by
        field_simp
      _ ≤ _ := h

/-- The first mass is exactly the zero mass times the sum of odds. -/
theorem coeff_bernoulliPolynomial_one {n : ℕ} (p : Fin n → ℝ)
    (hp1 : ∀ i, p i < 1) :
    (bernoulliPolynomial p).coeff 1 = (bernoulliPolynomial p).coeff 0 * oddsSum p := by
  cases n with
  | zero => simp [oddsSum, coeff_one]
  | succ n =>
    have hd := coeff_bernoulliPolynomial_derivative p 0
    simp only [Nat.cast_zero, zero_add, one_mul] at hd
    rw [hd, oddsSum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have h0 : (bernoulliPolynomial p).coeff 0 =
        (1 - p i) * (bernoulliPolynomial (omitCoin p i)).coeff 0 := by
      rw [bernoulliPolynomial_omit p i, add_mul]
      simp
    rw [h0]
    field_simp [(sub_pos.mpr (hp1 i)).ne']

theorem oddsSum_bounds {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpHalf : ∀ i, p i ≤ 1 / 2) :
    (∑ i, p i) ≤ oddsSum p ∧ oddsSum p ≤ 2 * ∑ i, p i := by
  have hpoint (i : Fin n) : p i ≤ p i / (1 - p i) ∧ p i / (1 - p i) ≤ 2 * p i := by
    have hi : 0 < 1 - p i := by linarith [hpHalf i]
    constructor
    · rw [le_div_iff₀ hi]
      nlinarith [sq_nonneg (p i)]
    · rw [div_le_iff₀ hi]
      nlinarith [mul_nonneg (hp i) (show 0 ≤ 1 - 2 * p i by linarith [hpHalf i])]
  constructor
  · exact Finset.sum_le_sum (fun i _ => (hpoint i).1)
  · dsimp [oddsSum]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => (hpoint i).2)

theorem coeff_bernoulliPolynomial_one_ge {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpHalf : ∀ i, p i ≤ 1 / 2) :
    (1 - ∑ i, p i) * (∑ i, p i) ≤ (bernoulliPolynomial p).coeff 1 := by
  rw [coeff_bernoulliPolynomial_one p (fun i => by linarith [hpHalf i])]
  exact mul_le_mul (coeff_bernoulliPolynomial_zero_ge p hp (fun i => by linarith [hpHalf i]))
    (oddsSum_bounds p hp hpHalf).1 (Finset.sum_nonneg (fun i _ => hp i))
    (coeff_bernoulliPolynomial_nonneg p hp (fun i => by linarith [hpHalf i]) 0)

end RenyiMonotonicity
