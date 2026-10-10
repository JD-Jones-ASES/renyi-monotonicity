module

public import RenyiMonotonicity.CMBDefinitions
public import Mathlib.Topology.Order.IntermediateValue

/-! Polynomial compactification of the beta-binomial shape parameter. -/

@[expose] public section
noncomputable section
open scoped BigOperators Topology

namespace RenyiMonotonicity

/-- The scaled ascending factorial extends regularly through reciprocal shape zero. -/
def compactMultichoose (u : ℝ) (k : ℕ) : ℝ :=
  (∏ j ∈ Finset.range k, (1+(j:ℝ)*u)) / k.factorial

def compactBetaWeight (u : ℝ) (N : ℕ) (k : Fin (N+1)) : ℝ :=
  compactMultichoose u k.val * compactMultichoose u (N-k.val)

def compactBetaMoment (N : ℕ) (u : ℝ) (ell : ℕ) : ℝ :=
  ∑ k : Fin (N+1), compactBetaWeight u N k * cmbGrid N k ^ ell

@[simp] theorem compactMultichoose_zero_degree (u : ℝ) : compactMultichoose u 0 = 1 := by
  simp [compactMultichoose]

theorem compactMultichoose_succ (u : ℝ) (k : ℕ) :
    compactMultichoose u (k+1) = (1+k*u)/(k+1)*compactMultichoose u k := by
  simp only [compactMultichoose, Finset.prod_range_succ, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one]
  field_simp
  ring_nf
  simp only [mul_comm, mul_left_comm, mul_assoc]

theorem compactMultichoose_pos (u : ℝ) (hu : 0 ≤ u) (k : ℕ) : 0 < compactMultichoose u k := by
  unfold compactMultichoose
  apply div_pos _ (by positivity)
  exact Finset.prod_pos (fun j _ => by positivity)

@[simp] theorem compactMultichoose_at_zero (k : ℕ) : compactMultichoose 0 k = 1 / k.factorial := by
  simp [compactMultichoose]

@[simp] theorem compactMultichoose_at_one (k : ℕ) : compactMultichoose 1 k = 1 := by
  induction k with
  | zero => simp
  | succ k ih => rw [compactMultichoose_succ, ih]; simp [add_comm, ne_of_gt (by positivity : (0:ℝ)<k+1)]

/-- The compactified factor is exactly the original shape factor times its scale. -/
theorem compactMultichoose_eq (u : ℝ) (hu : u ≠ 0) (k : ℕ) :
    compactMultichoose u k = u^k*Ring.multichoose (1/u) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [compactMultichoose_succ, ih, pow_succ]
    have H := real_multichoose_mul_succ (1/u) k
    have hk : (k:ℝ)+1 ≠ 0 := by positivity
    apply (mul_right_inj' hk).mp
    field_simp
    have hscale := congrArg (fun z : ℝ => u^k*u*z) H
    field_simp at hscale
    nlinarith [hscale]

/-- Compactified weights retain the same normalized law for positive reciprocal shape. -/
theorem compactBetaWeight_eq (u : ℝ) (hu : u ≠ 0) (N : ℕ) (k : Fin (N+1)) :
    compactBetaWeight u N k = u^N*betaBinomialWeight (1/u) N k.val := by
  rw [compactBetaWeight, compactMultichoose_eq u hu, compactMultichoose_eq u hu]
  simp only [betaBinomialWeight, show k.val ≤ N by omega, ↓reduceIte]
  rw [show u^k.val*Ring.multichoose (1/u) k.val*
      (u^(N-k.val)*Ring.multichoose (1/u) (N-k.val)) =
      (u^k.val*u^(N-k.val))*(Ring.multichoose (1/u) k.val*Ring.multichoose (1/u) (N-k.val)) by ring,
    ← pow_add, Nat.add_sub_of_le (show k.val ≤ N by omega)]

@[simp] theorem compactBetaWeight_at_one (N : ℕ) (k : Fin (N+1)) : compactBetaWeight 1 N k = 1 := by
  simp [compactBetaWeight]

/-- Reciprocal shape zero gives the binomial weights with their common factorial scale. -/
theorem compactBetaWeight_at_zero (N : ℕ) (k : Fin (N+1)) :
    compactBetaWeight 0 N k = (N.choose k.val : ℝ) / N.factorial := by
  have H := congrArg (fun x : ℕ => (x:ℝ)) (Nat.choose_mul_factorial_mul_factorial (show k.val ≤ N by omega))
  push_cast at H
  simp only [compactBetaWeight, compactMultichoose_at_zero]
  have hN : (N.factorial:ℝ) ≠ 0 := by positivity
  have hk : (k.val.factorial:ℝ) ≠ 0 := by positivity
  have hr : ((N-k.val).factorial:ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith [H]

theorem compactBetaMoment_pos (N : ℕ) (hN : N ≠ 0) (u : ℝ) (hu : 0 ≤ u) (ell : ℕ) :
    0 < compactBetaMoment N u ell := by
  apply Finset.sum_pos'
  · intro k _
    exact mul_nonneg (mul_pos (compactMultichoose_pos u hu _) (compactMultichoose_pos u hu _)).le
      (pow_nonneg (cmbGrid_nonneg _ _) _)
  · refine ⟨0, Finset.mem_univ _, ?_⟩
    simpa only [cmbGrid_zero N hN, one_pow, mul_one, compactBetaWeight, Fin.val_zero, Nat.sub_zero] using
      mul_pos (compactMultichoose_pos u hu 0) (compactMultichoose_pos u hu N)

theorem continuous_compactBetaMoment (N ell : ℕ) : Continuous (fun u => compactBetaMoment N u ell) := by
  unfold compactBetaMoment compactBetaWeight compactMultichoose
  fun_prop

@[simp] theorem compactBetaMoment_at_one (N ell : ℕ) : compactBetaMoment N 1 ell = cmbMoment N 0 ell := by
  simp [compactBetaMoment, cmbMoment]

theorem compactBetaMoment_at_zero (N ell : ℕ) :
    compactBetaMoment N 0 ell = cmbMoment N 1 ell / N.factorial := by
  simp only [compactBetaMoment, compactBetaWeight_at_zero, cmbMoment, Real.rpow_one]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem compactBetaMoment_eq (N : ℕ) (u : ℝ) (hu : u ≠ 0) (ell : ℕ) :
    compactBetaMoment N u ell = u^N*betaBinomialMoment N (1/u) ell := by
  simp only [compactBetaMoment, compactBetaWeight_eq u hu, betaBinomialMoment, Finset.mul_sum, mul_assoc]

end RenyiMonotonicity
