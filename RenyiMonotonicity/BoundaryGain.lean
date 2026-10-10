module
public import RenyiMonotonicity.BoundaryConvolution

@[expose] public section
noncomputable section
open Set
open scoped BigOperators Topology

namespace RenyiMonotonicity

theorem normalizedPair_nonneg {q a b : ℝ} (hq : q ≤ 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hba : b ≤ a) (hs1 : a + b ≤ 1) :
    0 ≤ normalizedPair q a b := by
  rcases eq_or_lt_of_le (add_nonneg ha hb) with hs | hs
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    simp [normalizedPair, ha0, hb0]
  · exact mul_nonneg (sub_nonneg.mpr hba) (entropyOrderKernel_nonneg hq hs hs1)

/-- The first new pair has a logarithmic gain uniformly through order one. -/
theorem normalizedPair_first_gain {q a b c ε : ℝ} (hq : q ≤ 1)
    (hc : 0 < c) (hε : 0 < ε) (hε1 : ε ≤ 1) (hb : 0 ≤ b)
    (ha : c * ε / 2 ≤ a) (hba : b ≤ a / 2) (hs : a + b ≤ ε) :
    (c / 4) * ε * (-Real.log ε) ≤ normalizedPair q a b := by
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hsum : 0 < a + b := add_pos_of_pos_of_nonneg ha0 hb
  have hd : c / 4 * ε ≤ a - b := by nlinarith
  have hw : -Real.log ε ≤ entropyOrderKernel q (a + b) :=
    (neg_le_neg (Real.log_le_log hsum hs)).trans (entropyOrderKernel_log_le hq hsum (hs.trans hε1))
  exact mul_le_mul hd hw (neg_nonneg.mpr (Real.log_nonpos hε.le hε1)) (by linarith)

/-- The logarithmic new-pair gain strictly dominates the old-pair loss on an
explicit small-coin collar. -/
theorem boundary_gain_dominates {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε)
    (hεsmall : ε ≤ Real.exp (-128 / c ^ 2)) :
    0 < -(16 / c) * ε + (c / 4) * ε * (-Real.log ε) := by
  have hl := Real.log_le_log hε hεsmall
  rw [Real.log_exp] at hl
  have hcoef : 16 / c < (c / 4) * (-Real.log ε) := by
    have hh := mul_le_mul_of_nonneg_left (neg_le_neg hl) (show 0 ≤ c / 4 by positivity)
    have he : (c / 4) * -(-128 / c ^ 2) = 32 / c := by field_simp; ring
    rw [he] at hh
    rw [show (32 : ℝ) / c = 2 * (16 / c) by ring] at hh
    have hpos : 0 < 16 / c := by positivity
    linarith
  nlinarith [mul_pos hε (sub_pos.mpr hcoef)]

/-- A nonnegative finite sum grows when more entries are included. -/
theorem sum_fin_mono_length (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k)
    {m n : ℕ} (hmn : m ≤ n) :
    (∑ i : Fin m, f i.val) ≤ ∑ i : Fin n, f i.val := by
  rw [Fin.sum_univ_eq_sum_range, Fin.sum_univ_eq_sum_range]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn) (fun k _ _ => hf k)

/-- Each coefficient perturbation is counted at most twice by the old pairs. -/
theorem sum_old_pair_perturbations_le (f : ℤ → ℝ) (hf : ∀ k, 0 ≤ f k)
    (hf0 : f (-1) = 0) {m N : ℕ} (hmN : m + 2 ≤ N) :
    (∑ k : Fin (m + 2), (f ((k.val : ℤ) - 1) + f (k.val : ℤ))) ≤
      2 * ∑ k : Fin N, f (k.val : ℤ) := by
  rw [Finset.sum_add_distrib]
  have hshift : (∑ k : Fin (m + 2), f ((k.val : ℤ) - 1)) =
      ∑ k : Fin (m + 1), f (k.val : ℤ) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.cast_zero, zero_sub, hf0, Fin.val_succ,
      Nat.cast_add, Nat.cast_one, add_sub_cancel_right, zero_add]
  rw [hshift]
  have h₁ := sum_fin_mono_length (fun k => f (k : ℤ)) (fun k => hf _) (show m + 1 ≤ N by omega)
  have h₂ := sum_fin_mono_length (fun k => f (k : ℤ)) (fun k => hf _) hmN
  linarith

end RenyiMonotonicity
