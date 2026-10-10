module

public import RenyiMonotonicity.BetaBinomial

@[expose] public section

open scoped BigOperators
open Polynomial

namespace RenyiMonotonicity

/-- Shifting the beta shape cancels a positive integer count exactly. -/
theorem real_multichoose_shape_step (a : ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * Ring.multichoose a (n + 1) = a * Ring.multichoose (a + 1) n := by
  have h₀ := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (a + 1) n
  have h₁ := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a (n + 1)
  rw [ascPochhammer_succ_left] at h₁
  simp only [Polynomial.smeval_mul, Polynomial.smeval_comp, Polynomial.smeval_add,
    Polynomial.smeval_X, Polynomial.smeval_one, nsmul_eq_mul,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_one, pow_zero, one_mul] at h₀ h₁
  rw [← h₀] at h₁
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hf
  nlinarith [h₁]

theorem real_multichoose_shape_shift (a : ℝ) (n : ℕ) :
    (a + n) * Ring.multichoose a n = a * Ring.multichoose (a + 1) n := by
  rw [← real_multichoose_mul_succ, real_multichoose_shape_step]

/-- The coefficient cancellation behind the entire function `F`. -/
theorem betaBinomialWeight_quadratic_shift (a : ℝ) (n k : ℕ) (hk : k ≤ n) :
    ((n + 2 : ℝ) ^ 2 - ((n : ℝ) - 2 * k) ^ 2) * betaBinomialWeight a (n + 2) (k + 1) =
      4 * a ^ 2 * betaBinomialWeight (a + 1) n k := by
  have h₀ := real_multichoose_shape_step a k
  have h₁ := real_multichoose_shape_step a (n - k)
  have H := congrArg₂ (fun x y : ℝ => x * y) h₀ h₁
  have he : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := by exact Nat.cast_sub hk
  rw [he] at H
  simp only [betaBinomialWeight, hk, show k + 1 ≤ n + 2 by omega, ↓reduceIte,
    show n + 2 - (k + 1) = (n - k) + 1 by omega]
  nlinarith [H]

/-- The finite weighted exponential sum representing `N²M−M''`. -/
noncomputable def betaBinomialF (a : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), ((N : ℝ) ^ 2 - ((N : ℝ) - 2 * k) ^ 2) *
    betaBinomialWeight a N k * Real.exp (((N : ℝ) - 2 * k) * t)

/-- The actual finite `F` identity, including the two vanishing endpoint terms. -/
theorem betaBinomialF_shift (a : ℝ) (n : ℕ) (t : ℝ) :
    betaBinomialF a (n + 2) t = 4 * a ^ 2 * betaBinomialMGF (a + 1) n t := by
  rw [betaBinomialF, betaBinomialMGF_eq_sum, Finset.mul_sum,
    Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [Nat.cast_zero, mul_zero, sub_zero, sub_self, zero_mul, add_zero]
  have hlast : ((n + 2 : ℝ) ^ 2 - ((n + 2 : ℝ) - 2 * (n + 2)) ^ 2) = 0 := by ring
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  rw [show (n + 1 : ℝ) + 1 = n + 2 by ring, hlast, zero_mul, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa using Finset.mem_range.mp hk
  have H := betaBinomialWeight_quadratic_shift a n k hk'
  have he : (n + 2 : ℝ) - 2 * (k + 1) = n - 2 * k := by ring
  rw [he, H]
  ring

/-- The first-moment cancellation at an interior pair of counts. -/
theorem multichoose_pair_difference (a : ℝ) (i j : ℕ) :
    ((j : ℝ) - i) * Ring.multichoose a (i + 1) * Ring.multichoose a (j + 1) =
      a * (Ring.multichoose (a + 1) (i + 1) * Ring.multichoose (a + 1) j -
        Ring.multichoose (a + 1) i * Ring.multichoose (a + 1) (j + 1)) := by
  have hi : (i : ℝ) + 1 ≠ 0 := by positivity
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  have h₀ : Ring.multichoose a (i + 1) = a * Ring.multichoose (a + 1) i / (i + 1) := by
    apply (eq_div_iff hi).mpr
    simpa [mul_comm] using real_multichoose_shape_step a i
  have h₁ : Ring.multichoose a (j + 1) = a * Ring.multichoose (a + 1) j / (j + 1) := by
    apply (eq_div_iff hj).mpr
    simpa [mul_comm] using real_multichoose_shape_step a j
  have h₂ : Ring.multichoose (a + 1) (i + 1) =
      (a + 1 + i) * Ring.multichoose (a + 1) i / (i + 1) := by
    apply (eq_div_iff hi).mpr
    simpa [mul_comm] using real_multichoose_mul_succ (a + 1) i
  have h₃ : Ring.multichoose (a + 1) (j + 1) =
      (a + 1 + j) * Ring.multichoose (a + 1) j / (j + 1) := by
    apply (eq_div_iff hj).mpr
    simpa [mul_comm] using real_multichoose_mul_succ (a + 1) j
  rw [h₀, h₁, h₂, h₃]
  field_simp
  ring

/-- The first-moment weight is an exact backward difference of the next
shape's degree-one-shorter weights. -/
theorem betaBinomialWeight_linear_shift (a : ℝ) (n k : ℕ) :
    ((n + 1 : ℝ) - 2 * k) * betaBinomialWeight a (n + 1) k =
      a * (betaBinomialWeight (a + 1) n k -
        if k = 0 then 0 else betaBinomialWeight (a + 1) n (k - 1)) := by
  cases k with
  | zero => simpa using real_multichoose_shape_step a n
  | succ k =>
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
      by_cases hk : k < n
      · let j := n - k - 1
        have H := multichoose_pair_difference a k j
        have hn : (j : ℝ) = n - k - 1 := by
          dsimp [j]
          rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), Nat.cast_one]
        rw [hn] at H
        simp only [betaBinomialWeight, show k + 1 ≤ n + 1 by omega,
          show k + 1 ≤ n by omega, show k ≤ n by omega, ↓reduceIte,
          show n + 1 - (k + 1) = j + 1 by dsimp [j]; omega,
          show n - (k + 1) = j by dsimp [j]; omega,
          show n - k = j + 1 by dsimp [j]; omega]
        push_cast
        nlinarith [H]
      · by_cases he : k = n
        · subst k
          have H := real_multichoose_shape_step a n
          simp only [betaBinomialWeight, le_refl, Nat.sub_self, Ring.multichoose_zero_right,
            mul_one, show ¬n + 1 ≤ n by omega, ↓reduceIte, zero_sub]
          push_cast
          nlinarith [H]
        · simp [betaBinomialWeight, show ¬ k + 1 ≤ n + 1 by omega,
            show ¬ k + 1 ≤ n by omega, show ¬ k ≤ n by omega]

/-- A finite backward-difference summation, retaining both endpoints. -/
theorem sum_backwardDifference (A E : ℕ → ℝ) (n : ℕ) (hA : A (n + 1) = 0) :
    (∑ k ∈ Finset.range (n + 2), (A k - if k = 0 then 0 else A (k - 1)) * E k) =
      ∑ k ∈ Finset.range (n + 1), A k * (E k - E (k + 1)) := by
  have H : (∑ k ∈ Finset.range (n + 1), A (k + 1) * E (k + 1)) + A 0 * E 0 =
      ∑ k ∈ Finset.range (n + 1), A k * E k := by
    rw [← Finset.sum_range_succ' (fun k => A k * E k) (n + 1)]
    rw [Finset.sum_range_succ, hA, zero_mul, add_zero]
  rw [Finset.sum_range_succ']
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
    Nat.add_sub_cancel, sub_zero, sub_mul, Finset.sum_sub_distrib,
    mul_sub]
  linarith [H]

/-- The derivative exponential sum has an exact shape-shift factorization. -/
theorem betaBinomialMGF_derivative_sum (a : ℝ) (n : ℕ) (t : ℝ) :
    (∑ k ∈ Finset.range (n + 2), ((n + 1 : ℝ) - 2 * k) *
      betaBinomialWeight a (n + 1) k * Real.exp (((n + 1 : ℝ) - 2 * k) * t)) =
      2 * a * Real.sinh t * betaBinomialMGF (a + 1) n t := by
  simp_rw [betaBinomialWeight_linear_shift, mul_assoc]
  rw [← Finset.mul_sum, sum_backwardDifference _ _ n (by simp [betaBinomialWeight])]
  rw [betaBinomialMGF_eq_sum, Real.sinh_eq]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have h₀ : Real.exp (((n + 1 : ℝ) - 2 * k) * t) =
      Real.exp t * Real.exp (((n : ℝ) - 2 * k) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h₁ : Real.exp (((n + 1 : ℝ) - 2 * (k + 1)) * t) =
      Real.exp (-t) * Real.exp (((n : ℝ) - 2 * k) * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [Nat.cast_add, Nat.cast_one]
  rw [h₀, h₁]
  ring

/-- Differentiation of the literal finite moment-generating function. -/
theorem hasDerivAt_betaBinomialMGF (a : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (betaBinomialMGF a n)
      (∑ k ∈ Finset.range (n + 1), ((n : ℝ) - 2 * k) * betaBinomialWeight a n k *
        Real.exp (((n : ℝ) - 2 * k) * t)) t := by
  have he : betaBinomialMGF a n = fun u => ∑ k ∈ Finset.range (n + 1),
      betaBinomialWeight a n k * Real.exp (((n : ℝ) - 2 * k) * u) := by
    funext u
    exact betaBinomialMGF_eq_sum a n u
  rw [he]
  apply HasDerivAt.fun_sum
  intro k hk
  convert (((Real.hasDerivAt_exp (((n : ℝ) - 2 * k) * t)).comp t
    ((hasDerivAt_id t).const_mul ((n : ℝ) - 2 * k))).const_mul (betaBinomialWeight a n k)) using 1 <;> first | rfl | ring

/-- The actual first derivative has the classical shifted-shape form. -/
theorem hasDerivAt_betaBinomialMGF_shift (a : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (betaBinomialMGF a (n + 1))
      (2 * a * Real.sinh t * betaBinomialMGF (a + 1) n t) t := by
  have H := hasDerivAt_betaBinomialMGF a (n + 1) t
  simpa only [Nat.cast_add, Nat.cast_one, betaBinomialMGF_derivative_sum] using H

/-- Differentiating twice remains a finite exact moment sum. -/
theorem hasDerivAt_deriv_betaBinomialMGF (a : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (deriv (betaBinomialMGF a n))
      (∑ k ∈ Finset.range (n + 1), ((n : ℝ) - 2 * k) ^ 2 * betaBinomialWeight a n k *
        Real.exp (((n : ℝ) - 2 * k) * t)) t := by
  have he : deriv (betaBinomialMGF a n) = fun u => ∑ k ∈ Finset.range (n + 1),
      ((n : ℝ) - 2 * k) * betaBinomialWeight a n k * Real.exp (((n : ℝ) - 2 * k) * u) := by
    funext u
    exact (hasDerivAt_betaBinomialMGF a n u).deriv
  rw [he]
  apply HasDerivAt.fun_sum
  intro k hk
  convert (((Real.hasDerivAt_exp (((n : ℝ) - 2 * k) * t)).comp t
    ((hasDerivAt_id t).const_mul ((n : ℝ) - 2 * k))).const_mul
      (((n : ℝ) - 2 * k) * betaBinomialWeight a n k)) using 1 <;> first | rfl | ring

/-- The finite definition of `F` agrees exactly with `N²M−M''`. -/
theorem betaBinomialF_eq_deriv (a : ℝ) (n : ℕ) (t : ℝ) :
    betaBinomialF a n t = (n : ℝ) ^ 2 * betaBinomialMGF a n t -
      deriv (deriv (betaBinomialMGF a n)) t := by
  rw [(hasDerivAt_deriv_betaBinomialMGF a n t).deriv, betaBinomialMGF_eq_sum,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The concrete Gegenbauer representation of `F`, with its exact constant. -/
theorem betaBinomialF_eq_gegenbauer (a : ℝ) (ha : 0 < a) (n : ℕ) (t : ℝ) :
    betaBinomialF a (n + 2) t =
      4 * a ^ 2 * (gegenbauerPolynomial (a + 1) n).eval (Real.cosh t) := by
  rw [betaBinomialF_shift, betaBinomialMGF_eq_gegenbauer _ (by linarith)]

/-- The concrete Gegenbauer representation of `M'`, before removal of the
factor `t` at the center. -/
theorem deriv_betaBinomialMGF_eq_gegenbauer (a : ℝ) (ha : 0 < a) (n : ℕ) (t : ℝ) :
    deriv (betaBinomialMGF a (n + 1)) t =
      2 * a * Real.sinh t * (gegenbauerPolynomial (a + 1) n).eval (Real.cosh t) := by
  rw [(hasDerivAt_betaBinomialMGF_shift a n t).deriv,
    betaBinomialMGF_eq_gegenbauer _ (by linarith)]

end RenyiMonotonicity
