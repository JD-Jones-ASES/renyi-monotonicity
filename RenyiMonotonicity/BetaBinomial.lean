module

public import RenyiMonotonicity.Gegenbauer
public import RenyiMonotonicity.HarmonicSeries

@[expose] public section

open scoped BigOperators
open Polynomial

namespace RenyiMonotonicity

/-- The ascending-factorial coefficient has this division-free recurrence. -/
theorem real_multichoose_mul_succ (a : ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * Ring.multichoose a (n + 1) =
      (a + n) * Ring.multichoose a n := by
  have h₀ := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n
  have h₁ := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a (n + 1)
  rw [ascPochhammer_succ_right] at h₁
  simp only [Polynomial.smeval_mul, Polynomial.smeval_add, Polynomial.smeval_X,
    Polynomial.smeval_natCast, nsmul_eq_mul, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one] at h₀ h₁
  rw [← h₀] at h₁
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  apply mul_left_cancel₀ hf
  nlinarith [h₁]

theorem real_multichoose_pos (a : ℝ) (ha : 0 < a) (n : ℕ) :
    0 < Ring.multichoose a n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h := real_multichoose_mul_succ a n
      have hp : 0 < (a + n) * Ring.multichoose a n := mul_pos (by positivity) ih
      have hn : 0 < (n : ℝ) + 1 := by positivity
      nlinarith

/-- The unnormalized symmetric beta-binomial weights. -/
noncomputable def betaBinomialWeight (a : ℝ) (N k : ℕ) : ℝ :=
  if k ≤ N then Ring.multichoose a k * Ring.multichoose a (N - k) else 0

@[simp] theorem betaBinomialWeight_zero (a : ℝ) (N : ℕ) :
    betaBinomialWeight a N 0 = Ring.multichoose a N := by
  simp [betaBinomialWeight]

theorem betaBinomialWeight_pos (a : ℝ) (ha : 0 < a) (N k : ℕ) (hk : k ≤ N) :
    0 < betaBinomialWeight a N k := by
  simp only [betaBinomialWeight, hk, ↓reduceIte]
  exact mul_pos (real_multichoose_pos a ha _) (real_multichoose_pos a ha _)

theorem betaBinomialWeight_reflect (a : ℝ) (N k : ℕ) (hk : k ≤ N) :
    betaBinomialWeight a N (N - k) = betaBinomialWeight a N k := by
  simp [betaBinomialWeight, hk, Nat.sub_sub_self hk, mul_comm]

/-- The finite recurrence coefficient identity at an interior index. -/
theorem multichoose_pair_recurrence (a : ℝ) (i j : ℕ) :
    ((i : ℝ) + j + 2) * Ring.multichoose a (i + 1) * Ring.multichoose a (j + 1) =
      (i + j + 1 + a) * (Ring.multichoose a (i + 1) * Ring.multichoose a j +
        Ring.multichoose a i * Ring.multichoose a (j + 1)) -
      (i + j + 2 * a) * Ring.multichoose a i * Ring.multichoose a j := by
  have hi : (i : ℝ) + 1 ≠ 0 := by positivity
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  have he₀ : Ring.multichoose a (i + 1) =
      (a + i) * Ring.multichoose a i / (i + 1) := by
    apply (eq_div_iff hi).mpr
    simpa [mul_comm] using real_multichoose_mul_succ a i
  have he₁ : Ring.multichoose a (j + 1) =
      (a + j) * Ring.multichoose a j / (j + 1) := by
    apply (eq_div_iff hj).mpr
    simpa [mul_comm] using real_multichoose_mul_succ a j
  rw [he₀, he₁]
  field_simp
  ring

/-- The generating polynomial of the actual unnormalized finite weights. -/
noncomputable def betaBinomialPolynomial (a : ℝ) (N : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range (N + 1), Polynomial.C (betaBinomialWeight a N k) * Polynomial.X ^ k

@[simp] theorem betaBinomialPolynomial_coeff (a : ℝ) (N k : ℕ) :
    (betaBinomialPolynomial a N).coeff k = betaBinomialWeight a N k := by
  simp only [betaBinomialPolynomial, finsetSum_coeff, coeff_C_mul_X_pow]
  by_cases hk : k < N + 1
  · simp [hk]
  · simp [hk, betaBinomialWeight, show ¬ k ≤ N by omega]

/-- The literal weight recurrence, with the predecessor handled by a separate
zero case rather than truncated subtraction at the left endpoint. -/
theorem betaBinomialWeight_recurrence_succ (a : ℝ) (n k : ℕ) :
    (n + 2 : ℝ) * betaBinomialWeight a (n + 2) (k + 1) =
      (n + 1 + a) * (betaBinomialWeight a (n + 1) (k + 1) + betaBinomialWeight a (n + 1) k) -
        (n + 2 * a) * betaBinomialWeight a n k := by
  by_cases hk : k ≤ n
  · have H := multichoose_pair_recurrence a k (n - k)
    have hn : (k : ℝ) + (n - k : ℕ) = n := by exact_mod_cast Nat.add_sub_of_le hk
    have he₀ : n + 2 - (k + 1) = (n - k) + 1 := by omega
    have he₁ : n + 1 - (k + 1) = n - k := by omega
    have he₂ : n + 1 - k = (n - k) + 1 := by omega
    simp only [betaBinomialWeight, show k + 1 ≤ n + 2 by omega,
      show k + 1 ≤ n + 1 by omega, show k ≤ n + 1 by omega, hk, ↓reduceIte, he₀, he₁, he₂]
    rw [show (k : ℝ) + (n - k : ℕ) + 2 = n + 2 by linarith] at H
    rw [hn] at H
    simpa only [mul_assoc] using H
  · by_cases he : k = n + 1
    · subst k
      simp only [betaBinomialWeight, le_refl, Nat.sub_self, Ring.multichoose_zero_right,
        mul_one, show ¬ n + 1 + 1 ≤ n + 1 by omega, show ¬ n + 1 ≤ n by omega,
        ↓reduceIte, zero_add, mul_zero, sub_zero]
      have H := real_multichoose_mul_succ a (n + 1)
      norm_num only [Nat.cast_add, Nat.cast_one, add_assoc, show (1 + 1 : ℝ) = 2 by norm_num] at H
      nlinarith [H]
    · simp [betaBinomialWeight, show ¬ k + 1 ≤ n + 2 by omega,
        show ¬ k + 1 ≤ n + 1 by omega, show ¬ k ≤ n + 1 by omega, hk]

theorem betaBinomialPolynomial_recurrence (a : ℝ) (n : ℕ) :
    C (n + 2 : ℝ) * betaBinomialPolynomial a (n + 2) =
      C (n + 1 + a) * ((1 + X) * betaBinomialPolynomial a (n + 1)) -
        C (n + 2 * a) * (X * betaBinomialPolynomial a n) := by
  ext k
  cases k with
  | zero =>
      simp only [betaBinomialPolynomial_coeff, betaBinomialWeight_zero,
        coeff_sub, mul_coeff_zero, coeff_add, coeff_one, coeff_C_zero, coeff_X_zero,
        add_zero, one_mul, ↓reduceIte]
      have H := real_multichoose_mul_succ a (n + 1)
      norm_num only [Nat.cast_add, Nat.cast_one, add_assoc, show (1 + 1 : ℝ) = 2 by norm_num,
        show n + (1 + 1) = n + 2 by omega] at H
      nlinarith [H]
  | succ k =>
      simp only [coeff_C_mul, coeff_sub, add_mul, one_mul, coeff_add, coeff_X_mul,
        betaBinomialPolynomial_coeff]
      nlinarith [betaBinomialWeight_recurrence_succ a n k]

/-- The classical leading coefficient converts the monic recurrence to its
usual Gegenbauer normalization. -/
noncomputable def gegenbauerScale (a : ℝ) (n : ℕ) : ℝ :=
  2 ^ n * Ring.multichoose a n

noncomputable def gegenbauerPolynomial (a : ℝ) (n : ℕ) : ℝ[X] :=
  C (gegenbauerScale a n) * monicGegenbauer a n

theorem gegenbauerScale_pos (a : ℝ) (ha : 0 < a) (n : ℕ) : 0 < gegenbauerScale a n :=
  mul_pos (pow_pos (by norm_num) _) (real_multichoose_pos a ha _)

theorem gegenbauerScale_succ (a : ℝ) (n : ℕ) :
    gegenbauerScale a (n + 1) = 2 * (a + n) / (n + 1) * gegenbauerScale a n := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have H := real_multichoose_mul_succ a n
  dsimp [gegenbauerScale]
  rw [pow_succ]
  field_simp
  nlinarith [congrArg (fun z : ℝ => (2 : ℝ) ^ n * z) H]

theorem gegenbauerPolynomial_recurrence (a : ℝ) (ha : 0 < a) (n : ℕ) :
    C (n + 2 : ℝ) * gegenbauerPolynomial a (n + 2) =
      C (2 * (n + 1 + a)) * (X * gegenbauerPolynomial a (n + 1)) -
        C (n + 2 * a) * gegenbauerPolynomial a n := by
  have hna : (n : ℝ) + a ≠ 0 := by positivity
  have hna1 : (n : ℝ) + a + 1 ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have h₁ : (n + 2 : ℝ) * gegenbauerScale a (n + 2) =
      2 * (n + 1 + a) * gegenbauerScale a (n + 1) := by
    rw [show n + 2 = (n + 1) + 1 by omega, gegenbauerScale_succ]
    push_cast
    field_simp
    ring
  have h₂ : (n + 2 : ℝ) * gegenbauerScale a (n + 2) * gegenbauerRecurrenceCoefficient a n =
      (n + 2 * a) * gegenbauerScale a n := by
    rw [h₁, gegenbauerScale_succ]
    dsimp [gegenbauerRecurrenceCoefficient]
    field_simp
    ring
  simp only [gegenbauerPolynomial, monicGegenbauer_recurrence]
  calc
    _ = C ((n + 2 : ℝ) * gegenbauerScale a (n + 2)) *
        (X * monicGegenbauer a (n + 1)) -
      C ((n + 2 : ℝ) * gegenbauerScale a (n + 2) * gegenbauerRecurrenceCoefficient a n) *
        monicGegenbauer a n := by simp only [map_mul]; ring
    _ = _ := by rw [h₂, h₁]; simp only [map_mul]; ring

/-- The actual finite exponential sum, written via its finite generating
polynomial so all endpoint weights are retained. -/
noncomputable def betaBinomialMGF (a : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp ((n : ℝ) * t) * (betaBinomialPolynomial a n).eval (Real.exp (-2 * t))

@[simp] theorem betaBinomialPolynomial_zero (a : ℝ) : betaBinomialPolynomial a 0 = 1 := by
  simp [betaBinomialPolynomial]

@[simp] theorem betaBinomialPolynomial_one (a : ℝ) : betaBinomialPolynomial a 1 = C a * (1 + X) := by
  simp [betaBinomialPolynomial, Finset.sum_range_succ, betaBinomialWeight]
  ring

@[simp] theorem gegenbauerPolynomial_zero (a : ℝ) : gegenbauerPolynomial a 0 = 1 := by
  simp [gegenbauerPolynomial, gegenbauerScale]

@[simp] theorem gegenbauerPolynomial_one (a : ℝ) : gegenbauerPolynomial a 1 = C (2 * a) * X := by
  simp [gegenbauerPolynomial, gegenbauerScale]

theorem betaBinomialMGF_recurrence (a : ℝ) (n : ℕ) (t : ℝ) :
    (n + 2 : ℝ) * betaBinomialMGF a (n + 2) t =
      2 * (n + 1 + a) * Real.cosh t * betaBinomialMGF a (n + 1) t -
        (n + 2 * a) * betaBinomialMGF a n t := by
  let E : ℕ → ℝ := fun j => Real.exp ((j : ℝ) * t)
  let z : ℝ := Real.exp (-2 * t)
  have h₂ : E (n + 2) * z = E n := by
    dsimp [E, z]
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have h₃ : E (n + 2) * (1 + z) = 2 * Real.cosh t * E (n + 1) := by
    rw [mul_add, mul_one, h₂]
    dsimp [E]
    rw [Real.cosh_eq]
    have hposExp : Real.exp t * Real.exp (((n + 1 : ℕ) : ℝ) * t) = Real.exp (((n + 2 : ℕ) : ℝ) * t) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    have hnegExp : Real.exp (-t) * Real.exp (((n + 1 : ℕ) : ℝ) * t) = Real.exp ((n : ℝ) * t) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    nlinarith [hposExp, hnegExp]
  have H := congrArg (fun P : ℝ[X] => P.eval z) (betaBinomialPolynomial_recurrence a n)
  simp only [eval_mul, eval_C, eval_sub, eval_add, eval_one, eval_X] at H
  change (n + 2 : ℝ) * (E (n + 2) * _) =
    2 * (n + 1 + a) * Real.cosh t * (E (n + 1) * _) - (n + 2 * a) * (E n * _)
  calc
    _ = E (n + 2) * ((n + 2 : ℝ) * (betaBinomialPolynomial a (n + 2)).eval z) := by ring
    _ = E (n + 2) * ((n + 1 + a) * ((1 + z) * (betaBinomialPolynomial a (n + 1)).eval z) -
        (n + 2 * a) * (z * (betaBinomialPolynomial a n).eval z)) := by rw [H]
    _ = (n + 1 + a) * (E (n + 2) * (1 + z)) * (betaBinomialPolynomial a (n + 1)).eval z -
        (n + 2 * a) * (E (n + 2) * z) * (betaBinomialPolynomial a n).eval z := by ring
    _ = _ := by rw [h₂, h₃]; ring

@[simp] theorem betaBinomialMGF_zero (a t : ℝ) : betaBinomialMGF a 0 t = 1 := by
  simp [betaBinomialMGF]

@[simp] theorem betaBinomialMGF_one (a t : ℝ) : betaBinomialMGF a 1 t = 2 * a * Real.cosh t := by
  have H : Real.exp t * Real.exp (-2 * t) = Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [betaBinomialMGF, betaBinomialPolynomial_one, Nat.cast_one, one_mul,
    eval_mul, eval_C, eval_add, eval_one, eval_X, Real.cosh_eq]
  nlinarith [congrArg (fun z : ℝ => a * z) H]

/-- The beta-binomial finite exponential sum is exactly the Gegenbauer
polynomial evaluated at `cosh`, with classical normalization. -/
theorem betaBinomialMGF_eq_gegenbauer (a : ℝ) (ha : 0 < a) (n : ℕ) (t : ℝ) :
    betaBinomialMGF a n t = (gegenbauerPolynomial a n).eval (Real.cosh t) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih₀ ih₁ =>
      have H := betaBinomialMGF_recurrence a n t
      have G := congrArg (fun P : ℝ[X] => P.eval (Real.cosh t)) (gegenbauerPolynomial_recurrence a ha n)
      simp only [eval_mul, eval_C, eval_sub, eval_X] at G
      rw [ih₀, ih₁] at H
      have hn : (n + 2 : ℝ) ≠ 0 := by positivity
      apply mul_left_cancel₀ hn
      nlinarith [H, G]

/-- Expansion into the actual finite symmetric exponential weights. The
integer count is cast before the subtraction in each exponent. -/
theorem betaBinomialMGF_eq_sum (a : ℝ) (n : ℕ) (t : ℝ) :
    betaBinomialMGF a n t = ∑ k ∈ Finset.range (n + 1),
      betaBinomialWeight a n k * Real.exp (((n : ℝ) - 2 * k) * t) := by
  simp only [betaBinomialMGF, betaBinomialPolynomial, eval_finsetSum,
    eval_mul, eval_C, eval_pow, eval_X, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← Real.exp_nat_mul]
  calc
    _ = betaBinomialWeight a n k * (Real.exp ((n : ℝ) * t) * Real.exp ((k : ℝ) * (-2 * t))) := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

end RenyiMonotonicity
