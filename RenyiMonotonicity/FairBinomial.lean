module

public import RenyiMonotonicity.MidpointSymmetry

@[expose] public section

namespace RenyiMonotonicity

/-- The fair-binomial mass, using the same integer zero extension as all count laws. -/
noncomputable def fairBinomialMass (n : ℕ) (k : ℤ) : ℝ :=
  bernoulliMass (fun _ : Fin n => (1 / 2 : ℝ)) k

/-- The exact generating polynomial of the fair count law. -/
theorem bernoulliPolynomial_all_half (n : ℕ) :
    bernoulliPolynomial (fun _ : Fin n => (1 / 2 : ℝ)) =
      Polynomial.C ((1 / 2 : ℝ) ^ n) * (Polynomial.X + 1) ^ n := by
  unfold bernoulliPolynomial
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [Polynomial.C_pow, ← mul_pow]
  congr 1
  norm_num
  ring

/-- The exact binomial coefficient formula, including indices beyond the support. -/
theorem fairBinomialMass_nat (n k : ℕ) :
    fairBinomialMass n (k : ℤ) = (1 / 2 : ℝ) ^ n * (n.choose k : ℝ) := by
  rw [fairBinomialMass, bernoulliMass_natCast, bernoulliPolynomial_all_half,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_add_one_pow]

theorem fairBinomialMass_neg (n : ℕ) (k : ℤ) (hk : k < 0) : fairBinomialMass n k = 0 :=
  bernoulliMass_neg _ k hk

theorem fairBinomialMass_above (n : ℕ) (k : ℤ) (hk : n < k) : fairBinomialMass n k = 0 :=
  bernoulliMass_eq_zero_above _ k hk

/-- Pascal convolution with a fair coin, on all integer indices. -/
theorem fairBinomialMass_succ (n : ℕ) (k : ℤ) :
    fairBinomialMass n k + fairBinomialMass n (k - 1) = 2 * fairBinomialMass (n + 1) k := by
  have hp : (fun _ : Fin (n + 1) => (1 / 2 : ℝ)) =
      Fin.cons (1 / 2 : ℝ) (fun _ : Fin n => (1 / 2 : ℝ)) := by
    ext i
    exact (Fin.cases (by simp) (fun j => by simp) i)
  unfold fairBinomialMass
  rw [hp, bernoulliMass_cons]
  ring

/-- The left adjacent-binomial identity, valid before and beyond both support
endpoints as well as on the positive support. -/
theorem fairBinomialMass_left_step (n : ℕ) (k : ℤ) :
    (n + 1 : ℝ) * fairBinomialMass n k =
      2 * ((n + 1 : ℝ) - k) * fairBinomialMass (n + 1) k := by
  by_cases hk0 : 0 ≤ k
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
    by_cases hk : k ≤ n + 1
    · have hchoose := congrArg (fun z : ℕ => (z : ℝ)) (Nat.choose_mul_succ_eq n k)
      push_cast [Nat.cast_sub hk] at hchoose
      simp only [fairBinomialMass_nat, pow_succ, Int.cast_natCast]
      nlinarith [congrArg (fun z : ℝ => (1 / 2 : ℝ) ^ n * z) hchoose]
    · have h₀ := fairBinomialMass_above n k (by omega)
      have h₁ := fairBinomialMass_above (n + 1) k (by omega)
      rw [h₀, h₁]
      ring
  · rw [fairBinomialMass_neg n k (by omega), fairBinomialMass_neg (n + 1) k (by omega)]
    ring

/-- The right adjacent-binomial identity, with integer predecessor subtraction. -/
theorem fairBinomialMass_right_step (n : ℕ) (k : ℤ) :
    (n + 1 : ℝ) * fairBinomialMass n (k - 1) =
      2 * (k : ℝ) * fairBinomialMass (n + 1) k := by
  have h₀ := fairBinomialMass_left_step n k
  have h₁ := fairBinomialMass_succ n k
  nlinarith

/-- The three second-order adjacent identities needed for one biased coin
among arbitrarily many fair ones. -/
theorem fairBinomialMass_two_steps (n : ℕ) (k : ℤ) :
    ((n + 1 : ℝ) * (n + 2)) * fairBinomialMass n k =
      4 * ((n + 2 : ℝ) - k) * ((n + 1 : ℝ) - k) * fairBinomialMass (n + 2) k ∧
    ((n + 1 : ℝ) * (n + 2)) * fairBinomialMass n (k - 1) =
      4 * (k : ℝ) * ((n + 2 : ℝ) - k) * fairBinomialMass (n + 2) k ∧
    ((n + 1 : ℝ) * (n + 2)) * fairBinomialMass n (k - 2) =
      4 * (k : ℝ) * ((k : ℝ) - 1) * fairBinomialMass (n + 2) k := by
  have h₀ := fairBinomialMass_left_step n k
  have h₁ := fairBinomialMass_left_step (n + 1) k
  have h₂ := fairBinomialMass_right_step n k
  have h₃ := fairBinomialMass_right_step n (k - 1)
  have h₄ := fairBinomialMass_right_step (n + 1) k
  have h₅ := fairBinomialMass_left_step (n + 1) (k - 1)
  push_cast at h₁ h₃ h₄ h₅
  rw [show k - 1 - 1 = k - 2 by omega] at h₃
  constructor
  · nlinarith [congrArg (fun z : ℝ => (n + 2 : ℝ) * z) h₀,
      congrArg (fun z : ℝ => (2 * ((n + 1 : ℝ) - k)) * z) h₁]
  constructor
  · nlinarith [congrArg (fun z : ℝ => (n + 2 : ℝ) * z) h₂,
      congrArg (fun z : ℝ => (2 * (k : ℝ)) * z) h₁]
  · nlinarith [congrArg (fun z : ℝ => (n + 2 : ℝ) * z) h₃,
      congrArg (fun z : ℝ => (2 * ((k : ℝ) - 1)) * z) h₄]

end RenyiMonotonicity
