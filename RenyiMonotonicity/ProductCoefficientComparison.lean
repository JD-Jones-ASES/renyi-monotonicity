module

public import RenyiMonotonicity.RealRootedDifferences

@[expose] public section

open scoped BigOperators Topology
open Filter
open Polynomial

namespace RenyiMonotonicity

/-- The finite positive-factor products used in the entire-product comparison. -/
noncomputable def linearFactorProduct {n : ℕ} (u : Fin n → ℝ) : ℝ[X] :=
  ∏ i, (1 + Polynomial.C (u i) * Polynomial.X)

@[simp] theorem linearFactorProduct_empty (u : Fin 0 → ℝ) : linearFactorProduct u = 1 := by
  simp [linearFactorProduct]

theorem linearFactorProduct_cons {n : ℕ} (a : ℝ) (u : Fin n → ℝ) :
    linearFactorProduct (Fin.cons a u) = (1 + C a * X) * linearFactorProduct u := by
  simp [linearFactorProduct, Fin.prod_univ_succ]

@[simp] theorem linearFactorProduct_coeff_zero {n : ℕ} (u : Fin n → ℝ) :
    (linearFactorProduct u).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp [linearFactorProduct, Polynomial.eval_prod]

theorem coeff_mul_positiveFactor_succ (P : ℝ[X]) (a : ℝ) (k : ℕ) :
    ((1 + C a * X) * P).coeff (k + 1) = P.coeff (k + 1) + a * P.coeff k := by
  rw [add_mul, one_mul, mul_assoc, coeff_add, coeff_C_mul, coeff_X_mul]

theorem linearFactorProduct_coeff_nonneg {n : ℕ} (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i)
    (k : ℕ) : 0 ≤ (linearFactorProduct u).coeff k := by
  induction n generalizing k with
  | zero => simp [coeff_one]; split <;> norm_num
  | succ n ih =>
      have he : u = Fin.cons (u 0) (Fin.tail u) := (Fin.cons_self_tail u).symm
      rw [he, linearFactorProduct_cons]
      cases k with
      | zero => simp [← linearFactorProduct_cons]
      | succ k =>
        rw [coeff_mul_positiveFactor_succ]
        exact add_nonneg (ih _ (fun i => hu _) _) (mul_nonneg (hu 0) (ih _ (fun i => hu _) _))

theorem linearFactorProduct_coeff_pos {n : ℕ} (u : Fin n → ℝ) (hu : ∀ i, 0 < u i)
    (k : ℕ) (hk : k ≤ n) : 0 < (linearFactorProduct u).coeff k := by
  induction n generalizing k with
  | zero =>
      have : k = 0 := by omega
      simp [this]
  | succ n ih =>
      have he : u = Fin.cons (u 0) (Fin.tail u) := (Fin.cons_self_tail u).symm
      rw [he, linearFactorProduct_cons]
      cases k with
      | zero => simp [← linearFactorProduct_cons]
      | succ k =>
        rw [coeff_mul_positiveFactor_succ]
        exact add_pos_of_nonneg_of_pos
          (linearFactorProduct_coeff_nonneg _ (fun i => (hu _).le) _)
          (mul_pos (hu 0) (ih _ (fun i => hu _) _ (by omega)))

theorem linearFactorProduct_splits {n : ℕ} (u : Fin n → ℝ) :
    (linearFactorProduct u).Splits := by
  apply Polynomial.Splits.prod
  intro i _
  apply Polynomial.Splits.of_natDegree_le_one
  compute_degree

/-- Newton's inequality gives unnormalized coefficient log-concavity,
including vanishing outer coefficients. -/
theorem linearFactorProduct_logconcave {n : ℕ} (u : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ u i) (k : ℕ) :
    (linearFactorProduct u).coeff k * (linearFactorProduct u).coeff (k + 2) ≤
      (linearFactorProduct u).coeff (k + 1) ^ 2 := by
  have H := newton_coefficient_inequality _ (linearFactorProduct_splits u) k
  have hz := mul_nonneg (linearFactorProduct_coeff_nonneg u hu k)
    (linearFactorProduct_coeff_nonneg u hu (k + 2))
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- Increasing one positive linear factor increases every adjacent
coefficient ratio. This is the elementary comparison behind §7. -/
theorem linearFactorProduct_single_ratio {n : ℕ} (u : Fin n → ℝ)
    (hu : ∀ i, 0 < u i) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (k : ℕ) (hk : k ≤ n) :
    (linearFactorProduct (Fin.cons a u)).coeff (k + 1) /
        (linearFactorProduct (Fin.cons a u)).coeff k ≤
      (linearFactorProduct (Fin.cons b u)).coeff (k + 1) /
        (linearFactorProduct (Fin.cons b u)).coeff k := by
  have hap : ∀ i : Fin (n + 1), 0 < (Fin.cons a u : Fin (n + 1) → ℝ) i := by intro i; refine Fin.cases ha (fun j => hu j) i
  have hbp : ∀ i : Fin (n + 1), 0 < (Fin.cons b u : Fin (n + 1) → ℝ) i := by intro i; refine Fin.cases (ha.trans_le hab) (fun j => hu j) i
  have hd₀ := linearFactorProduct_coeff_pos (Fin.cons a u) hap k (by omega)
  have hd₁ := linearFactorProduct_coeff_pos (Fin.cons b u) hbp k (by omega)
  rw [div_le_div_iff₀ hd₀ hd₁]
  simp only [linearFactorProduct_cons]
  cases k with
  | zero =>
      simp only [coeff_mul_positiveFactor_succ, mul_coeff_zero, coeff_add, coeff_one,
        coeff_X_zero, mul_zero, add_zero, linearFactorProduct_coeff_zero,
        ite_true, mul_one]
      linarith
  | succ k =>
      simp only [coeff_mul_positiveFactor_succ]
      have H := linearFactorProduct_logconcave u (fun i => (hu i).le) k
      have H' := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr H)
      nlinarith

/-- Arbitrary-coordinate factorization of a positive linear-factor product. -/
theorem linearFactorProduct_update_eq_cons {n : ℕ} (u : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) (a : ℝ) :
    linearFactorProduct (Function.update u i a) =
      linearFactorProduct (Fin.cons a (omitCoin u i)) := by
  rw [linearFactorProduct_cons]
  unfold linearFactorProduct omitCoin
  rw [Fin.prod_univ_succAbove _ i]
  simp

/-- Every adjacent coefficient ratio is coordinatewise increasing in the
positive factors. Finite coordinate replacement proves the full comparison. -/
theorem linearFactorProduct_ratio_mono {n : ℕ} (u v : Fin n → ℝ)
    (hu : ∀ i, 0 < u i) (huv : ∀ i, u i ≤ v i) (k : ℕ) (hk : k < n) :
    (linearFactorProduct u).coeff (k + 1) / (linearFactorProduct u).coeff k ≤
      (linearFactorProduct v).coeff (k + 1) / (linearFactorProduct v).coeff k := by
  classical
  cases n with
  | zero => omega
  | succ n =>
      let R : (Fin (n + 1) → ℝ) → ℝ := fun w =>
        (linearFactorProduct w).coeff (k + 1) / (linearFactorProduct w).coeff k
      have haux (s : Finset (Fin (n + 1))) : R u ≤ R (s.piecewise v u) := by
        induction s using Finset.induction_on with
        | empty => simp
        | @insert i s hi ih =>
            rw [Finset.piecewise_insert]
            have hw (j) : 0 < s.piecewise v u j := by
              by_cases hj : j ∈ s
              · simpa [Finset.piecewise, hj] using (hu j).trans_le (huv j)
              · simpa [Finset.piecewise, hj] using hu j
            have hv : s.piecewise v u i = u i := Finset.piecewise_eq_of_notMem _ _ _ hi
            have hc := linearFactorProduct_single_ratio (omitCoin (s.piecewise v u) i)
              (fun j => hw _) (u i) (v i) (hu i) (huv i) k (by omega)
            rw [← linearFactorProduct_update_eq_cons, ← linearFactorProduct_update_eq_cons] at hc
            have he : Function.update (s.piecewise v u) i (u i) = s.piecewise v u := by
              rw [← hv]
              exact Function.update_eq_self _ _
            rw [he] at hc
            exact ih.trans hc
      simpa only [Finset.piecewise_univ] using haux Finset.univ

/-- The finite-product coefficient quotient decreases with its index when
the first product's positive factors are coordinatewise smaller. -/
theorem linearFactorProduct_quotient_antitone_step {n : ℕ} (u v : Fin n → ℝ)
    (hu : ∀ i, 0 < u i) (huv : ∀ i, u i ≤ v i) (k : ℕ) (hk : k < n) :
    (linearFactorProduct u).coeff (k + 1) / (linearFactorProduct v).coeff (k + 1) ≤
      (linearFactorProduct u).coeff k / (linearFactorProduct v).coeff k := by
  have h := linearFactorProduct_ratio_mono u v hu huv k hk
  have h₀ := linearFactorProduct_coeff_pos u hu k hk.le
  have hv : ∀ i, 0 < v i := fun i => (hu i).trans_le (huv i)
  have h₁ := linearFactorProduct_coeff_pos v hv k hk.le
  have h₂ := linearFactorProduct_coeff_pos v hv (k + 1) hk
  rw [div_le_div_iff₀ h₀ h₁] at h
  rw [div_le_div_iff₀ h₂ h₁]
  nlinarith

/-- Passing finite coefficient comparisons to an infinite product needs only
convergence of its fixed coefficients. The actual analytic products supply
these limits separately. -/
theorem coefficientComparison_of_finiteProductLimits (u v : ℕ → ℝ)
    (hu : ∀ j, 0 < u j) (huv : ∀ j, u j ≤ v j) (F G : ℕ → ℝ)
    (hF : ∀ k, Tendsto (fun n => (linearFactorProduct (fun j : Fin n => u j.val)).coeff k)
      atTop (𝓝 (F k)))
    (hG : ∀ k, Tendsto (fun n => (linearFactorProduct (fun j : Fin n => v j.val)).coeff k)
      atTop (𝓝 (G k))) (k : ℕ) :
    F (k + 1) * G k ≤ F k * G (k + 1) := by
  apply le_of_tendsto_of_tendsto ((hF (k + 1)).mul (hG k)) ((hF k).mul (hG (k + 1)))
  filter_upwards [eventually_ge_atTop (k + 1)] with n hn
  have h := linearFactorProduct_ratio_mono (fun j : Fin n => u j.val)
    (fun j : Fin n => v j.val) (fun j => hu _) (fun j => huv _) k (by omega)
  have h₀ := linearFactorProduct_coeff_pos (fun j : Fin n => u j.val) (fun j => hu _) k (by omega)
  have h₁ := linearFactorProduct_coeff_pos (fun j : Fin n => v j.val)
    (fun j => (hu _).trans_le (huv _)) k (by omega)
  rw [div_le_div_iff₀ h₀ h₁] at h
  nlinarith

end RenyiMonotonicity
