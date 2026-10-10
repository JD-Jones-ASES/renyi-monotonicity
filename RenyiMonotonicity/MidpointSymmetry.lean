module

public import RenyiMonotonicity.GradientSigns
public import RenyiMonotonicity.NormalizedMidpoint

@[expose] public section

namespace RenyiMonotonicity

/-- Complementing the coins reverses the full adjacent edge array. -/
theorem edgeSum_complement {n : ℕ} (p : Fin n → ℝ) (k : Fin (n + 2)) :
    edgeSum (fun i => 1 - p i) k = edgeSum p k.rev := by
  simp only [edgeSum, bernoulliMass_complement]
  have he : ((k.rev.val : ℕ) : ℤ) = (n : ℤ) + 1 - k.val := by
    rw [Fin.val_rev]
    omega
  rw [he, show (n : ℤ) - ((k.val : ℤ) - 1) = n + 1 - k.val by omega,
    show (n : ℤ) + 1 - k.val - 1 = n - k.val by omega]
  exact add_comm _ _

theorem edgeDifference_complement {n : ℕ} (p : Fin n → ℝ) (k : Fin (n + 2)) :
    edgeDifference (fun i => 1 - p i) k = -edgeDifference p k.rev := by
  simp only [edgeDifference, bernoulliMass_complement]
  have he : ((k.rev.val : ℕ) : ℤ) = (n : ℤ) + 1 - k.val := by
    rw [Fin.val_rev]
    omega
  rw [he, show (n : ℤ) - ((k.val : ℤ) - 1) = n + 1 - k.val by omega,
    show (n : ℤ) + 1 - k.val - 1 = n - k.val by omega]
  ring

/-- Both midpoint signs reverse under complementation, at every order. -/
theorem midpointFunctional_complement {n : ℕ} (q : ℝ) (p : Fin n → ℝ) :
    midpointFunctional q (fun i => 1 - p i) = -midpointFunctional q p := by
  simp only [midpointFunctional, edgeDifference_complement, edgeSum_complement, neg_mul,
    Finset.sum_neg_distrib]
  congr 1
  exact Equiv.sum_comp (Fin.revPerm)
    (fun k : Fin (n + 2) => edgeDifference p k * edgeSum p k ^ (q - 1))

theorem normalizedMidpointFunctional_complement {n : ℕ} (q : ℝ) (p : Fin n → ℝ) :
    normalizedMidpointFunctional q (fun i => 1 - p i) = -normalizedMidpointFunctional q p := by
  simp only [normalizedMidpointFunctional, edgeDifference_complement, edgeSum_complement, neg_mul,
    Finset.sum_neg_distrib]
  congr 1
  exact Equiv.sum_comp (Fin.revPerm)
    (fun k : Fin (n + 2) => edgeDifference p k * entropyOrderKernel q (edgeSum p k))

/-- Every all-fair count law has zero midpoint functional, with no restriction
on the real order or the number of fair coins. -/
@[simp] theorem midpointFunctional_all_half (n : ℕ) (q : ℝ) :
    midpointFunctional q (fun _ : Fin n => (1 / 2 : ℝ)) = 0 := by
  have h := midpointFunctional_complement q (fun _ : Fin n => (1 / 2 : ℝ))
  norm_num at h
  linarith

@[simp] theorem normalizedMidpointFunctional_all_half (n : ℕ) (q : ℝ) :
    normalizedMidpointFunctional q (fun _ : Fin n => (1 / 2 : ℝ)) = 0 := by
  have h := normalizedMidpointFunctional_complement q (fun _ : Fin n => (1 / 2 : ℝ))
  norm_num at h
  linarith

end RenyiMonotonicity
