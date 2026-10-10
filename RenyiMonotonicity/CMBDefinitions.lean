module

public import RenyiMonotonicity.BetaBinomial

/-! Actual finite Conway-Maxwell-binomial and symmetric beta-binomial even moments. -/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace RenyiMonotonicity

def cmbGrid (N : ℕ) (k : Fin (N+1)) : ℝ := (((N:ℝ)-2*k.val)/N)^2

def cmbMoment (N : ℕ) (q : ℝ) (ell : ℕ) : ℝ :=
  ∑ k : Fin (N+1), (N.choose k.val:ℝ)^q*(cmbGrid N k)^ell

def betaBinomialMoment (N : ℕ) (a : ℝ) (ell : ℕ) : ℝ :=
  ∑ k : Fin (N+1), betaBinomialWeight a N k.val*(cmbGrid N k)^ell

lemma cmbGrid_nonneg (N : ℕ) (k : Fin (N+1)) : 0≤cmbGrid N k := sq_nonneg _

lemma cmbGrid_zero (N : ℕ) (hN : N≠0) : cmbGrid N 0=1 := by
  simp [cmbGrid,hN]

lemma cmbMoment_pos (N : ℕ) (hN : N≠0) (q : ℝ) (ell : ℕ) : 0<cmbMoment N q ell := by
  apply Finset.sum_pos'
  · intro k _
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (cmbGrid_nonneg _ _) _)
  · refine ⟨0,Finset.mem_univ _,?_⟩
    simp [cmbGrid_zero N hN]

lemma betaBinomialMoment_pos (N : ℕ) (hN : N≠0) (a : ℝ) (ha : 0<a) (ell : ℕ) :
    0<betaBinomialMoment N a ell := by
  apply Finset.sum_pos'
  · intro k _
    exact mul_nonneg (betaBinomialWeight_pos a ha N k.val (by omega)).le (pow_nonneg (cmbGrid_nonneg _ _) _)
  · refine ⟨0,Finset.mem_univ _,?_⟩
    simp only [cmbGrid_zero N hN,one_pow,mul_one,Fin.val_zero]
    exact betaBinomialWeight_pos a ha N 0 (Nat.zero_le _)

end RenyiMonotonicity
