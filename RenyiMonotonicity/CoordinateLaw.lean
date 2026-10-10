module

public import RenyiMonotonicity.CoefficientLemmas

@[expose] public section

open scoped BigOperators

namespace RenyiMonotonicity

/-- Remove one coordinate, retaining the induced order of all other coordinates. -/
def omitCoin {n : ℕ} (p : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : Fin n → ℝ :=
  p ∘ i.succAbove

/-- Single-coordinate factorization of the actual generating polynomial. -/
theorem bernoulliPolynomial_omit {n : ℕ} (p : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    bernoulliPolynomial p =
      (Polynomial.C (1 - p i) + Polynomial.C (p i) * Polynomial.X) *
        bernoulliPolynomial (omitCoin p i) := by
  unfold bernoulliPolynomial omitCoin
  exact Fin.prod_univ_succAbove _ i

@[simp] theorem omitCoin_update {n : ℕ} (p : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (t : ℝ) : omitCoin (Function.update p i t) i = omitCoin p i := by
  funext j
  simp [omitCoin]

theorem bernoulliPolynomial_update {n : ℕ} (p : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (t : ℝ) :
    bernoulliPolynomial (Function.update p i t) =
      (Polynomial.C (1 - t) + Polynomial.C t * Polynomial.X) *
        bernoulliPolynomial (omitCoin p i) := by
  rw [bernoulliPolynomial_omit _ i]
  simp

theorem bernoulliPolynomial_update_eq_cons {n : ℕ} (p : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (t : ℝ) :
    bernoulliPolynomial (Function.update p i t) =
      bernoulliPolynomial (Fin.cons t (omitCoin p i)) := by
  rw [bernoulliPolynomial_update, bernoulliPolynomial_cons]

/-- Deleting any zero coin preserves every integer-indexed mass. -/
theorem bernoulliMass_omit_zero {n : ℕ} (p : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (hi : p i = 0) (k : ℤ) :
    bernoulliMass p k = bernoulliMass (omitCoin p i) k := by
  simp [bernoulliMass, bernoulliPolynomial_omit p i, hi]

/-- Coordinate dependence is affine, with both outer masses supplied by zero extension. -/
theorem bernoulliMass_update {n : ℕ} (p : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (t : ℝ) (k : ℤ) :
    bernoulliMass (Function.update p i t) k =
      (1 - t) * bernoulliMass (omitCoin p i) k +
        t * bernoulliMass (omitCoin p i) (k - 1) := by
  have heq : bernoulliMass (Function.update p i t) k =
      bernoulliMass (Fin.cons t (omitCoin p i)) k := by
    simp only [bernoulliMass, bernoulliPolynomial_update_eq_cons]
  rw [heq, bernoulliMass_cons]

/-- The one-coordinate derivative is an exact finite difference of the omitted law. -/
theorem hasDerivAt_bernoulliMass_update {n : ℕ} (p : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (t : ℝ) (k : ℤ) :
    HasDerivAt (fun u => bernoulliMass (Function.update p i u) k)
      (bernoulliMass (omitCoin p i) (k - 1) - bernoulliMass (omitCoin p i) k) t := by
  simp only [bernoulliMass_update]
  simpa only [Pi.sub_apply, Pi.add_apply, Pi.add_def, Pi.sub_def, id_eq, zero_sub, zero_add, one_mul,
    neg_one_mul, sub_eq_add_neg, add_comm] using
    (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul_const
      (bernoulliMass (omitCoin p i) k)).add
        ((hasDerivAt_id t).mul_const (bernoulliMass (omitCoin p i) (k - 1)))

/-- The finite count-law coordinate derivative, including counts zero and `n+1`. -/
theorem hasDerivAt_bernoulliSum_update {n : ℕ} (p : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (t : ℝ) (k : Fin (n + 2)) :
    HasDerivAt (fun u => bernoulliSum (Function.update p i u) k)
      (bernoulliMass (omitCoin p i) ((k.val : ℤ) - 1) -
        bernoulliMass (omitCoin p i) (k.val : ℤ)) t := by
  simpa only [bernoulliMass_natCast, bernoulliSum] using
    hasDerivAt_bernoulliMass_update p i t (k.val : ℤ)

/-- Actual Bernoulli masses are nonnegative at every integer count. -/
theorem bernoulliMass_nonneg {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (k : ℤ) :
    0 ≤ bernoulliMass p k := by
  by_cases hk : 0 ≤ k
  · simp only [bernoulliMass, ite_eq_left hk]
    exact coeff_bernoulliPolynomial_nonneg p hp hp1 k.toNat
  · simp [bernoulliMass, hk]

end RenyiMonotonicity
