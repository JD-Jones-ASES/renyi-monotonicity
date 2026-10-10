module

public import RenyiMonotonicity.CoordinateLaw

@[expose] public section

open scoped BigOperators

namespace RenyiMonotonicity

/-- Collision probability of the concrete Bernoulli count law. -/
noncomputable def collision {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  ∑ k, bernoulliSum p k ^ 2

/-- Squared adjacent finite differences, with both outer zero masses included. -/
noncomputable def adjacentEnergy {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  ∑ k : Fin (n + 2),
    (bernoulliMass p ((k.val : ℤ) - 1) - bernoulliMass p (k.val : ℤ)) ^ 2

theorem adjacentEnergy_nonneg {n : ℕ} (p : Fin n → ℝ) : 0 ≤ adjacentEnergy p :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem sum_mass_sq {n : ℕ} (p : Fin n → ℝ) :
    (∑ k : Fin (n + 2), bernoulliMass p (k.val : ℤ) ^ 2) = collision p := by
  rw [Fin.sum_univ_castSucc]
  simp [collision, bernoulliSum]

theorem sum_shift_mass_sq {n : ℕ} (p : Fin n → ℝ) :
    (∑ k : Fin (n + 2), bernoulliMass p ((k.val : ℤ) - 1) ^ 2) = collision p := by
  rw [Fin.sum_univ_succ]
  simp [collision, bernoulliSum, Nat.cast_add, Nat.cast_one]

/-- Exact collision identity for addition of one coin, with no parameter assumptions. -/
theorem collision_cons {n : ℕ} (p : Fin n → ℝ) (t : ℝ) :
    collision (Fin.cons t p) = collision p - t * (1 - t) * adjacentEnergy p := by
  have hpoint (k : Fin (n + 2)) :
      bernoulliSum (Fin.cons t p) k ^ 2 =
        (1 - t) * bernoulliMass p (k.val : ℤ) ^ 2 +
        t * bernoulliMass p ((k.val : ℤ) - 1) ^ 2 -
        t * (1 - t) *
          (bernoulliMass p ((k.val : ℤ) - 1) - bernoulliMass p (k.val : ℤ)) ^ 2 := by
    change (bernoulliPolynomial (Fin.cons t p)).coeff k.val ^ 2 = _
    rw [← bernoulliMass_natCast (Fin.cons t p) k.val]
    rw [bernoulliMass_cons]
    ring
  change (∑ k : Fin (n + 2), bernoulliSum (Fin.cons t p) k ^ 2) =
    collision p - t * (1 - t) * adjacentEnergy p
  simp_rw [hpoint, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_mass_sq, sum_shift_mass_sq]
  change (1 - t) * collision p + t * collision p - t * (1 - t) * adjacentEnergy p = _
  ring

theorem collision_update {n : ℕ} (p : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (t : ℝ) :
    collision (Function.update p i t) =
      collision (omitCoin p i) - t * (1 - t) * adjacentEnergy (omitCoin p i) := by
  rw [← collision_cons]
  simp only [collision, bernoulliSum, bernoulliPolynomial_update_eq_cons]

/-- Increasing any coordinate up to one half decreases collision probability. -/
theorem collision_update_antitone {n : ℕ} (p : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (s t : ℝ) (hst : s ≤ t) (ht : t ≤ 1 / 2) :
    collision (Function.update p i t) ≤ collision (Function.update p i s) := by
  rw [collision_update, collision_update]
  have hst' : s * (1 - s) ≤ t * (1 - t) := by
    have hprod : 0 ≤ (t - s) * (1 - s - t) :=
      mul_nonneg (sub_nonneg.mpr hst) (by linarith)
    nlinarith
  exact sub_le_sub_left (mul_le_mul_of_nonneg_right hst' (adjacentEnergy_nonneg _)) _

/-- Finite coordinate replacement gives the full collision comparison. -/
theorem collision_antitone {n : ℕ} (p r : Fin n → ℝ)
    (hpr : ∀ i, p i ≤ r i) (hr : ∀ i, r i ≤ 1 / 2) : collision r ≤ collision p := by
  classical
  cases n with
  | zero =>
      have h : p = r := Subsingleton.elim _ _
      rw [h]
  | succ n =>
      have haux (s : Finset (Fin (n + 1))) : collision (s.piecewise r p) ≤ collision p := by
        induction s using Finset.induction_on with
        | empty => simp
        | @insert i s hi ih =>
            rw [Finset.piecewise_insert]
            have hc := collision_update_antitone (s.piecewise r p) i (p i) (r i) (hpr i) (hr i)
            have hv : s.piecewise r p i = p i := Finset.piecewise_eq_of_notMem _ _ _ hi
            have hu : Function.update (s.piecewise r p) i (p i) = s.piecewise r p := by
              rw [← hv]
              exact Function.update_eq_self _ _
            rw [hu] at hc
            exact hc.trans ih
      simpa only [Finset.piecewise_univ] using haux Finset.univ

/-- Normalization guarantees nonzero collision, even for signed parameter inputs. -/
theorem collision_pos {n : ℕ} (p : Fin n → ℝ) : 0 < collision p := by
  have hnonneg : 0 ≤ collision p := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_contra h
  have hz : collision p = 0 := le_antisymm (le_of_not_gt h) hnonneg
  have hg : ∀ k ∈ Finset.univ, bernoulliSum p k = 0 := (Finset.sum_sq_eq_zero_iff Finset.univ (bernoulliSum p)).mp hz
  have hsum : ∑ k, bernoulliSum p k = 0 := Finset.sum_eq_zero hg
  rw [sum_bernoulliSum] at hsum
  norm_num at hsum

@[simp] theorem powerSum_two_bernoulliSum {n : ℕ} (p : Fin n → ℝ) :
    powerSum 2 (bernoulliSum p) = collision p := by
  simp [powerSum, collision]

@[simp] theorem tsallis_two_bernoulliSum {n : ℕ} (p : Fin n → ℝ) :
    tsallis 2 (bernoulliSum p) = 1 - collision p := by
  norm_num [tsallis]
  ring

@[simp] theorem renyi_two_bernoulliSum {n : ℕ} (p : Fin n → ℝ) :
    renyi 2 (bernoulliSum p) = -Real.log (collision p) := by
  norm_num [renyi]
  ring

/-- Full order-two Tsallis monotonicity, including every support and fair boundary. -/
theorem tsallis_two_monotone {n : ℕ} (p r : Fin n → ℝ)
    (_hp : ∀ i, 0 ≤ p i) (hpr : ∀ i, p i ≤ r i) (hr : ∀ i, r i ≤ 1 / 2) :
    tsallis 2 (bernoulliSum p) ≤ tsallis 2 (bernoulliSum r) := by
  simp only [tsallis_two_bernoulliSum]
  exact sub_le_sub_left (collision_antitone p r hpr hr) 1

/-- Full order-two Rényi monotonicity, including every support and fair boundary. -/
theorem renyi_two_monotone {n : ℕ} (p r : Fin n → ℝ)
    (_hp : ∀ i, 0 ≤ p i) (hpr : ∀ i, p i ≤ r i) (hr : ∀ i, r i ≤ 1 / 2) :
    renyi 2 (bernoulliSum p) ≤ renyi 2 (bernoulliSum r) := by
  simp only [renyi_two_bernoulliSum]
  exact neg_le_neg (Real.log_le_log (collision_pos r) (collision_antitone p r hpr hr))

end RenyiMonotonicity
