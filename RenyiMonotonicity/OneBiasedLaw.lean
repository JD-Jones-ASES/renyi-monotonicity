module

public import RenyiMonotonicity.FairBinomial

@[expose] public section

namespace RenyiMonotonicity

/-- One distinguished coin followed by `m` fair coins. -/
noncomputable def oneBiasedParameters (m : ℕ) (p : ℝ) : Fin (m + 1) → ℝ :=
  Fin.cons p (fun _ => 1 / 2)

/-- The symmetric count-grid coordinate used in the binomial-escort moments. -/
noncomputable def binomialGridPoint (N : ℕ) (k : ℤ) : ℝ :=
  ((N : ℝ) - 2 * k) / N

theorem oneBiasedMass (m : ℕ) (p : ℝ) (k : ℤ) :
    bernoulliMass (oneBiasedParameters m p) k =
      (1 - p) * fairBinomialMass m k + p * fairBinomialMass m (k - 1) :=
  bernoulliMass_cons _ _ _

/-- The exact adjacent sum for the one-biased-plus-fair family, including both
outer support nodes. -/
theorem oneBiased_edgeSum (m : ℕ) (p : ℝ) (k : Fin (m + 1 + 2)) :
    edgeSum (oneBiasedParameters m p) k =
      2 * fairBinomialMass (m + 2) k.val *
        (1 + (1 - 2 * p) * binomialGridPoint (m + 2) k.val) := by
  have H := fairBinomialMass_two_steps m k.val
  have hd : ((m : ℝ) + 1) * (m + 2) ≠ 0 := by positivity
  have h₀ : fairBinomialMass m k.val =
      4 * ((m + 2 : ℝ) - k.val) * ((m + 1 : ℝ) - k.val) *
        fairBinomialMass (m + 2) k.val / ((m + 1 : ℝ) * (m + 2)) := by
    apply (eq_div_iff hd).mpr
    simpa only [Int.cast_natCast, mul_comm] using H.1
  have h₁ : fairBinomialMass m ((k.val : ℤ) - 1) =
      4 * (k.val : ℝ) * ((m + 2 : ℝ) - k.val) *
        fairBinomialMass (m + 2) k.val / ((m + 1 : ℝ) * (m + 2)) := by
    apply (eq_div_iff hd).mpr
    simpa only [Int.cast_natCast, mul_comm] using H.2.1
  have h₂ : fairBinomialMass m ((k.val : ℤ) - 2) =
      4 * (k.val : ℝ) * ((k.val : ℝ) - 1) *
        fairBinomialMass (m + 2) k.val / ((m + 1 : ℝ) * (m + 2)) := by
    apply (eq_div_iff hd).mpr
    simpa only [Int.cast_natCast, mul_comm] using H.2.2
  simp only [edgeSum, oneBiasedMass, show (k.val : ℤ) - 1 - 1 = k.val - 2 by omega,
    h₀, h₁, h₂, binomialGridPoint, Nat.cast_add, Nat.cast_ofNat, Int.cast_natCast]
  field_simp
  ring

/-- The exact signed adjacent difference for this family. Every predecessor
is formed in the integer zero extension. -/
theorem oneBiased_edgeDifference (m : ℕ) (p : ℝ) (k : Fin (m + 1 + 2)) :
    edgeDifference (oneBiasedParameters m p) k =
      2 * fairBinomialMass (m + 2) k.val *
        (-binomialGridPoint (m + 2) k.val + (1 - 2 * p) *
          (1 - (m + 2 : ℝ) * binomialGridPoint (m + 2) k.val ^ 2) / (m + 1)) := by
  have H := fairBinomialMass_two_steps m k.val
  have hd : ((m : ℝ) + 1) * (m + 2) ≠ 0 := by positivity
  have h₀ : fairBinomialMass m k.val =
      4 * ((m + 2 : ℝ) - k.val) * ((m + 1 : ℝ) - k.val) *
        fairBinomialMass (m + 2) k.val / ((m + 1 : ℝ) * (m + 2)) := by
    apply (eq_div_iff hd).mpr
    simpa only [Int.cast_natCast, mul_comm] using H.1
  have h₁ : fairBinomialMass m ((k.val : ℤ) - 1) =
      4 * (k.val : ℝ) * ((m + 2 : ℝ) - k.val) *
        fairBinomialMass (m + 2) k.val / ((m + 1 : ℝ) * (m + 2)) := by
    apply (eq_div_iff hd).mpr
    simpa only [Int.cast_natCast, mul_comm] using H.2.1
  have h₂ : fairBinomialMass m ((k.val : ℤ) - 2) =
      4 * (k.val : ℝ) * ((k.val : ℝ) - 1) *
        fairBinomialMass (m + 2) k.val / ((m + 1 : ℝ) * (m + 2)) := by
    apply (eq_div_iff hd).mpr
    simpa only [Int.cast_natCast, mul_comm] using H.2.2
  simp only [edgeDifference, oneBiasedMass, show (k.val : ℤ) - 1 - 1 = k.val - 2 by omega,
    h₀, h₁, h₂, binomialGridPoint, Nat.cast_add, Nat.cast_ofNat, Int.cast_natCast]
  field_simp
  ring

end RenyiMonotonicity
