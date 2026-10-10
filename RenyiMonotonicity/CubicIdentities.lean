module

public import RenyiMonotonicity.CoordinateLaw

@[expose] public section

open scoped BigOperators
open Polynomial

namespace RenyiMonotonicity

/-- The three-row contiguous Toeplitz determinant, expanded without division. -/
def toeplitzCubic (a b c d e : ℝ) : ℝ :=
  c ^ 3 - 2 * b * c * d + a * d ^ 2 + b ^ 2 * e - a * c * e

/-- The polynomial expansion is exactly the conventional three-row determinant. -/
theorem toeplitzCubic_eq_det (a b c d e : ℝ) :
    toeplitzCubic a b c d e = Matrix.det !![c, d, e; b, c, d; a, b, c] := by
  simp [Matrix.det_fin_three, toeplitzCubic]
  ring

/-- The first omitted-law cubic expansion, including vanishing outer entries. -/
theorem omitted_cubic_left (p a b c d e : ℝ) :
    ((1 - p) * c + p * b) * (c ^ 2 - b * d) +
      ((1 - p) * e + p * d) * (b ^ 2 - a * c) -
      ((1 - p) * d + p * c) * (b * c - a * d) =
        (1 - p) * toeplitzCubic a b c d e := by
  unfold toeplitzCubic
  ring

/-- The reflected omitted-law cubic expansion. -/
theorem omitted_cubic_right (p a b c d e : ℝ) :
    ((1 - p) * d + p * c) * (c ^ 2 - b * d) +
      ((1 - p) * b + p * a) * (d ^ 2 - c * e) -
      ((1 - p) * c + p * b) * (c * d - b * e) =
        p * toeplitzCubic a b c d e := by
  unfold toeplitzCubic
  ring

private theorem erase_prod_eq_omit {n : ℕ} (p : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    (∏ j ∈ Finset.univ.erase i,
      (Polynomial.C (1 - p j) + Polynomial.C (p j) * Polynomial.X)) =
        bernoulliPolynomial (omitCoin p i) := by
  rw [Fin.univ_succAbove n i, Finset.erase_cons]
  simp [bernoulliPolynomial, omitCoin, Finset.prod_map]

/-- Differentiate the actual Bernoulli product, with one coin omitted in each term. -/
theorem derivative_bernoulliPolynomial {n : ℕ} (p : Fin (n + 1) → ℝ) :
    Polynomial.derivative (bernoulliPolynomial p) =
      ∑ i, Polynomial.C (p i) * bernoulliPolynomial (omitCoin p i) := by
  classical
  change Polynomial.derivative (∏ i, (Polynomial.C (1 - p i) +
    Polynomial.C (p i) * Polynomial.X)) = _
  rw [Polynomial.derivative_prod_finset]
  apply Finset.sum_congr rfl
  intro i _
  rw [erase_prod_eq_omit]
  simp only [Polynomial.derivative_add, Polynomial.derivative_C,
    Polynomial.derivative_mul, Polynomial.derivative_X, zero_add, zero_mul,
    mul_one]
  exact mul_comm _ _

/-- The paired omitted-product polynomial. Its two variables record two counts. -/
noncomputable def omittedPairPolynomial {n : ℕ} (p : Fin (n + 1) → ℝ) :
    Polynomial (Polynomial ℝ) :=
  ∑ i, Polynomial.C (Polynomial.C (p i * (1 - p i))) *
    (bernoulliPolynomial (omitCoin p i)).map Polynomial.C *
    Polynomial.C (bernoulliPolynomial (omitCoin p i))

/-- Bivariate product identity underlying Hillion--Johnson's coefficient identities.
Both sides are formed from the concrete Bernoulli polynomial and actual omitted laws. -/
theorem bernoulli_bivariate_identity {n : ℕ} (p : Fin (n + 1) → ℝ) :
    (Polynomial.X - Polynomial.C Polynomial.X) * omittedPairPolynomial p =
      Polynomial.X * (Polynomial.derivative (bernoulliPolynomial p)).map Polynomial.C *
        Polynomial.C (bernoulliPolynomial p) -
      Polynomial.C (Polynomial.X * Polynomial.derivative (bernoulliPolynomial p)) *
        (bernoulliPolynomial p).map Polynomial.C := by
  classical
  rw [omittedPairPolynomial, Finset.mul_sum]
  have heach (i : Fin (n + 1)) :
      (Polynomial.X - Polynomial.C Polynomial.X) *
        (Polynomial.C (Polynomial.C (p i * (1 - p i))) *
          (bernoulliPolynomial (omitCoin p i)).map Polynomial.C *
          Polynomial.C (bernoulliPolynomial (omitCoin p i))) =
      Polynomial.X * (Polynomial.C (p i) * bernoulliPolynomial (omitCoin p i)).map Polynomial.C *
          Polynomial.C (bernoulliPolynomial p) -
      Polynomial.C (Polynomial.X * (Polynomial.C (p i) * bernoulliPolynomial (omitCoin p i))) *
          (bernoulliPolynomial p).map Polynomial.C := by
    rw [bernoulliPolynomial_omit p i]
    simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C,
      Polynomial.map_X, Polynomial.map_sub, Polynomial.map_one,
      map_mul, map_add, map_sub, map_one]
    ring
  simp_rw [heach]
  rw [Finset.sum_sub_distrib]
  simp only [derivative_bernoulliPolynomial, Polynomial.map_sum, map_sum,
    Finset.mul_sum, Finset.sum_mul]

/-- Every bivariate coefficient is the actual weighted product of omitted masses. -/
theorem coeff_omittedPairPolynomial {n : ℕ} (p : Fin (n + 1) → ℝ) (k l : ℕ) :
    ((omittedPairPolynomial p).coeff k).coeff l =
      ∑ i, p i * (1 - p i) *
        (bernoulliPolynomial (omitCoin p i)).coeff k *
        (bernoulliPolynomial (omitCoin p i)).coeff l := by
  classical
  unfold omittedPairPolynomial
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul, Polynomial.coeff_map]
  apply Finset.sum_congr rfl
  intro i _
  rw [← map_mul, Polynomial.coeff_C_mul]

/-- Coefficient form of the bivariate identity away from its two zero edges. -/
theorem bernoulli_coefficient_cross_identity {n : ℕ} (p : Fin (n + 1) → ℝ)
    (k l : ℕ) :
    (∑ i, p i * (1 - p i) *
      ((bernoulliPolynomial (omitCoin p i)).coeff k *
          (bernoulliPolynomial (omitCoin p i)).coeff (l + 1) -
        (bernoulliPolynomial (omitCoin p i)).coeff (k + 1) *
          (bernoulliPolynomial (omitCoin p i)).coeff l)) =
      ((k : ℝ) - l) * (bernoulliPolynomial p).coeff (k + 1) *
        (bernoulliPolynomial p).coeff (l + 1) := by
  have h := congrArg (fun Q : Polynomial (Polynomial ℝ) =>
    (Q.coeff (k + 1)).coeff (l + 1)) (bernoulli_bivariate_identity p)
  simp only [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul,
    Polynomial.coeff_C_mul, Polynomial.coeff_mul_C, Polynomial.coeff_map,
    Polynomial.coeff_derivative] at h
  simp only [coeff_omittedPairPolynomial] at h
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  simp only [mul_sub, ← mul_assoc] at h ⊢
  nlinarith [h]

/-- The zero inner edge of the bivariate identity; no predecessor is truncated. -/
theorem bernoulli_coefficient_edge_identity {n : ℕ} (p : Fin (n + 1) → ℝ)
    (k : ℕ) :
    (∑ i, p i * (1 - p i) *
      (bernoulliPolynomial (omitCoin p i)).coeff k *
      (bernoulliPolynomial (omitCoin p i)).coeff 0) =
      ((k : ℝ) + 1) * (bernoulliPolynomial p).coeff (k + 1) *
        (bernoulliPolynomial p).coeff 0 := by
  have h := congrArg (fun Q : Polynomial (Polynomial ℝ) =>
    (Q.coeff (k + 1)).coeff 0) (bernoulli_bivariate_identity p)
  simp only [sub_mul, Polynomial.coeff_sub, Polynomial.coeff_X_mul,
    Polynomial.coeff_X_mul_zero, Polynomial.coeff_C_mul, Polynomial.coeff_mul_C,
    Polynomial.coeff_map, Polynomial.coeff_derivative, sub_zero, zero_mul] at h
  simp only [coeff_omittedPairPolynomial] at h
  simp only [mul_sub] at h ⊢
  nlinarith [h]

/-- Two-row omitted minor identity, with genuine integer zero extension at the left edge. -/
theorem bernoulli_adjacent_minor_sum {n : ℕ} (p : Fin (n + 1) → ℝ) (k : ℤ) :
    (∑ i, p i * (1 - p i) *
      (bernoulliMass (omitCoin p i) k ^ 2 -
        bernoulliMass (omitCoin p i) (k - 1) * bernoulliMass (omitCoin p i) (k + 1))) =
      bernoulliMass p k * bernoulliMass p (k + 1) := by
  by_cases hk : 0 ≤ k
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    cases k with
    | zero =>
      simpa [bernoulliMass, pow_two, mul_assoc, mul_comm, mul_left_comm] using
        bernoulli_coefficient_edge_identity p 0
    | succ k =>
      have h := bernoulli_coefficient_cross_identity p (k + 1) k
      have e₁ : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
      have e₂ : ((k + 1 : ℕ) : ℤ) + 1 = ((k + 2 : ℕ) : ℤ) := by omega
      simp only [e₁, e₂, bernoulliMass_natCast]
      simpa [Nat.cast_add, pow_two, mul_comm, mul_left_comm, mul_assoc] using h
  · have hneg : k < 0 := lt_of_not_ge hk
    have hpred : k - 1 < 0 := by omega
    simp [bernoulliMass_neg _ _ hneg, bernoulliMass_neg _ _ hpred]

/-- Distance-two omitted minor identity, valid for every integer count. -/
theorem bernoulli_distance_two_minor_sum {n : ℕ} (p : Fin (n + 1) → ℝ) (k : ℤ) :
    (∑ i, p i * (1 - p i) *
      (bernoulliMass (omitCoin p i) k * bernoulliMass (omitCoin p i) (k + 1) -
        bernoulliMass (omitCoin p i) (k - 1) * bernoulliMass (omitCoin p i) (k + 2))) =
      2 * bernoulliMass p k * bernoulliMass p (k + 2) := by
  by_cases hk : 0 ≤ k
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    cases k with
    | zero =>
      have h := bernoulli_coefficient_edge_identity p 1
      norm_num [bernoulliMass, mul_assoc, mul_comm, mul_left_comm] at h ⊢
      exact h
    | succ k =>
      have h := bernoulli_coefficient_cross_identity p (k + 2) k
      have e₁ : ((k + 1 : ℕ) : ℤ) - 1 = (k : ℤ) := by omega
      have e₂ : ((k + 1 : ℕ) : ℤ) + 1 = ((k + 2 : ℕ) : ℤ) := by omega
      have e₃ : ((k + 1 : ℕ) : ℤ) + 2 = ((k + 3 : ℕ) : ℤ) := by omega
      simp only [e₁, e₂, e₃, bernoulliMass_natCast]
      simpa [Nat.cast_add, mul_comm, mul_left_comm, mul_assoc] using h
  · have hneg : k < 0 := lt_of_not_ge hk
    have hpred : k - 1 < 0 := by omega
    simp [bernoulliMass_neg _ _ hneg, bernoulliMass_neg _ _ hpred]

/-- The actual count law is the convolution with any selected omitted coin. -/
theorem bernoulliMass_eq_omit {n : ℕ} (p : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (k : ℤ) :
    bernoulliMass p k = (1 - p i) * bernoulliMass (omitCoin p i) k +
      p i * bernoulliMass (omitCoin p i) (k - 1) := by
  simpa using bernoulliMass_update p i (p i) k

/-- The omitted law's actual three-row Toeplitz minor. -/
noncomputable def omittedToeplitzCubic {n : ℕ} (p : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (k : ℤ) : ℝ :=
  toeplitzCubic (bernoulliMass (omitCoin p i) (k - 2))
    (bernoulliMass (omitCoin p i) (k - 1)) (bernoulliMass (omitCoin p i) k)
    (bernoulliMass (omitCoin p i) (k + 1)) (bernoulliMass (omitCoin p i) (k + 2))

/-- Hillion--Johnson Appendix A (33), proved for the concrete Bernoulli law.
The identity requires no probability or positivity assumptions. -/
theorem bernoulli_cubic_left {n : ℕ} (p : Fin (n + 1) → ℝ) (k : ℤ) :
    bernoulliMass p k ^ 2 * bernoulliMass p (k + 1) +
      bernoulliMass p (k - 1) * bernoulliMass p k * bernoulliMass p (k + 2) -
      2 * bernoulliMass p (k - 1) * bernoulliMass p (k + 1) ^ 2 =
        ∑ i, p i * (1 - p i) ^ 2 * omittedToeplitzCubic p i k := by
  have h₀ := bernoulli_adjacent_minor_sum p k
  have h₁ := bernoulli_adjacent_minor_sum p (k - 1)
  have h₂ := bernoulli_distance_two_minor_sum p (k - 1)
  have e₁ : k - 1 - 1 = k - 2 := by omega
  have e₂ : k - 1 + 1 = k := by omega
  have e₃ : k - 1 + 2 = k + 1 := by omega
  simp only [e₁, e₂, e₃] at h₁ h₂
  calc
    _ = bernoulliMass p k *
          (∑ i, p i * (1 - p i) *
            (bernoulliMass (omitCoin p i) k ^ 2 -
              bernoulliMass (omitCoin p i) (k - 1) *
                bernoulliMass (omitCoin p i) (k + 1))) +
        bernoulliMass p (k + 2) *
          (∑ i, p i * (1 - p i) *
            (bernoulliMass (omitCoin p i) (k - 1) ^ 2 -
              bernoulliMass (omitCoin p i) (k - 2) *
                bernoulliMass (omitCoin p i) k)) -
        bernoulliMass p (k + 1) *
          (∑ i, p i * (1 - p i) *
            (bernoulliMass (omitCoin p i) (k - 1) * bernoulliMass (omitCoin p i) k -
              bernoulliMass (omitCoin p i) (k - 2) *
                bernoulliMass (omitCoin p i) (k + 1))) := by
      rw [h₀, h₁, h₂]
      ring
    _ = _ := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [bernoulliMass_eq_omit p i k, bernoulliMass_eq_omit p i (k + 1),
        bernoulliMass_eq_omit p i (k + 2)]
      have e₄ : k + 1 - 1 = k := by omega
      have e₅ : k + 2 - 1 = k + 1 := by omega
      simp only [e₄, e₅, omittedToeplitzCubic, toeplitzCubic]
      ring

/-- Hillion--Johnson Appendix A (34), including every zero-extension boundary. -/
theorem bernoulli_cubic_right {n : ℕ} (p : Fin (n + 1) → ℝ) (k : ℤ) :
    bernoulliMass p k * bernoulliMass p (k + 1) ^ 2 +
      bernoulliMass p (k - 1) * bernoulliMass p (k + 1) * bernoulliMass p (k + 2) -
      2 * bernoulliMass p k ^ 2 * bernoulliMass p (k + 2) =
        ∑ i, p i ^ 2 * (1 - p i) * omittedToeplitzCubic p i k := by
  have h₀ := bernoulli_adjacent_minor_sum p k
  have h₁ := bernoulli_adjacent_minor_sum p (k + 1)
  have h₂ := bernoulli_distance_two_minor_sum p k
  have e₁ : k + 1 - 1 = k := by omega
  have e₂ : k + 1 + 1 = k + 2 := by omega
  simp only [e₁, e₂] at h₁
  calc
    _ = bernoulliMass p (k + 1) *
          (∑ i, p i * (1 - p i) *
            (bernoulliMass (omitCoin p i) k ^ 2 -
              bernoulliMass (omitCoin p i) (k - 1) *
                bernoulliMass (omitCoin p i) (k + 1))) +
        bernoulliMass p (k - 1) *
          (∑ i, p i * (1 - p i) *
            (bernoulliMass (omitCoin p i) (k + 1) ^ 2 -
              bernoulliMass (omitCoin p i) k *
                bernoulliMass (omitCoin p i) (k + 2))) -
        bernoulliMass p k *
          (∑ i, p i * (1 - p i) *
            (bernoulliMass (omitCoin p i) k * bernoulliMass (omitCoin p i) (k + 1) -
              bernoulliMass (omitCoin p i) (k - 1) *
                bernoulliMass (omitCoin p i) (k + 2))) := by
      rw [h₀, h₁, h₂]
      ring
    _ = _ := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [bernoulliMass_eq_omit p i k, bernoulliMass_eq_omit p i (k - 1),
        bernoulliMass_eq_omit p i (k + 1)]
      have e₃ : k - 1 - 1 = k - 2 := by omega
      simp only [e₁, e₃, omittedToeplitzCubic, toeplitzCubic]
      ring

end RenyiMonotonicity
