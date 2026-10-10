module

public import RenyiMonotonicity.FairFlux
public import RenyiMonotonicity.MidpointFunctional
public import RenyiMonotonicity.MixingGrid
public import RenyiMonotonicity.ToeplitzMinors

@[expose] public section

namespace RenyiMonotonicity

open scoped BigOperators

/-- The finite flux sum has only its two exterior boundary values. -/
theorem sum_fairFlux_telescope (q : ℝ) (h : ℤ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (fairFlux q (h ((k : ℤ) - 2)) (h ((k : ℤ) - 1)) -
      fairFlux q (h ((k : ℤ) - 1)) (h (k : ℤ)))) =
      fairFlux q (h (-2)) (h (-1)) - fairFlux q (h ((N : ℤ) - 2)) (h ((N : ℤ) - 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      rw [show (N : ℤ) + 1 - 2 = (N : ℤ) - 1 by omega,
        show (N : ℤ) + 1 - 1 = (N : ℤ) by omega]
      ring

/-- The strictly positive fair-face sum is obtained from local log-concavity
and a telescoping correction. Zero outer entries are retained literally. -/
theorem sum_fairLocalTerm_pos (q : ℝ) (h : ℤ → ℝ) (n : ℕ)
    (hq₀ : 0 < q) (hq₁ : q < 1) (hh : ∀ k, 0 ≤ h k)
    (hlc : ∀ k, h (k - 1) * h (k + 1) ≤ h k ^ 2)
    (hleft : ∀ k < 0, h k = 0) (hright : ∀ k, (n : ℤ) < k → h k = 0)
    (hzero : 0 < h 0) :
    0 < ∑ k : Fin (n + 3), fairLocalTerm q (h ((k.val : ℤ) - 2))
      (h ((k.val : ℤ) - 1)) (h (k.val : ℤ)) := by
  have hnonneg (k : ℕ) : 0 ≤ fairLocalTerm q (h ((k : ℤ) - 2))
      (h ((k : ℤ) - 1)) (h (k : ℤ)) +
      fairFlux q (h ((k : ℤ) - 2)) (h ((k : ℤ) - 1)) -
      fairFlux q (h ((k : ℤ) - 1)) (h (k : ℤ)) := by
    apply fairLocalTerm_add_flux_nonneg q _ _ _ hq₀ hq₁ (hh _) (hh _) (hh _)
    simpa only [sub_sub, show (1 : ℤ) + 1 = 2 by omega, sub_add_cancel] using hlc ((k : ℤ) - 1)
  have hstrict : 0 < fairLocalTerm q (h (-1)) (h 0) (h 1) +
      fairFlux q (h (-1)) (h 0) - fairFlux q (h 0) (h 1) := by
    apply fairLocalTerm_add_flux_pos q _ _ _ hq₀ hq₁ (hh _) hzero (hh _)
    rw [hleft (-1) (by omega), zero_mul]
    exact sq_pos_of_pos hzero
  have hsum := Finset.sum_pos' (s := Finset.range (n + 3))
    (fun k _ => hnonneg k) ⟨1, by simp, by simpa using hstrict⟩
  have hf := sum_fairFlux_telescope q h (n + 3)
  rw [hleft (-2) (by omega), hleft (-1) (by omega),
    hright ((n + 3 : ℕ) - 2) (by omega), hright ((n + 3 : ℕ) - 1) (by omega)] at hf
  simp only [sub_self] at hf
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => fairLocalTerm q (h ((k : ℤ) - 2))
    (h ((k : ℤ) - 1)) (h (k : ℤ))) (n + 3)]
  have hs : (∑ k ∈ Finset.range (n + 3),
      (fairLocalTerm q (h ((k : ℤ) - 2)) (h ((k : ℤ) - 1)) (h (k : ℤ)) +
      fairFlux q (h ((k : ℤ) - 2)) (h ((k : ℤ) - 1)) -
      fairFlux q (h ((k : ℤ) - 1)) (h (k : ℤ)))) =
      ∑ k ∈ Finset.range (n + 3), fairLocalTerm q (h ((k : ℤ) - 2))
        (h ((k : ℤ) - 1)) (h (k : ℤ)) := by
    simp_rw [add_sub_assoc]
    rw [Finset.sum_add_distrib, hf, add_zero]
  rwa [hs] at hsum

/-- The actual law satisfies the global log-concavity premise, including the
zero extension on both sides of its support. -/
theorem bernoulliMass_logconcave {n : ℕ} (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp₁ : ∀ i, p i ≤ 1) (k : ℤ) :
    bernoulliMass p (k - 1) * bernoulliMass p (k + 1) ≤ bernoulliMass p k ^ 2 := by
  have h := bernoulli_toeplitzTwo_nonneg p hp hp₁ 0 1 k (k + 1) (by omega) (by omega)
  simp only [toeplitzTwo, sub_zero, add_sub_cancel_right] at h
  nlinarith

/-- Strict positivity of the fair-face derivative sum for the actual coefficient
law, allowing zero coins and all support-changing edges. -/
theorem sum_fairLocalTerm_bernoulli_pos {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hq₀ : 0 < q) (hq₁ : q < 1) (hp : ∀ i, 0 ≤ p i) (hp₁ : ∀ i, p i < 1) :
    0 < ∑ k : Fin (n + 3), fairLocalTerm q (bernoulliMass p ((k.val : ℤ) - 2))
      (bernoulliMass p ((k.val : ℤ) - 1)) (bernoulliMass p (k.val : ℤ)) := by
  apply sum_fairLocalTerm_pos q (bernoulliMass p) n hq₀ hq₁
    (bernoulliMass_nonneg p hp (fun i => (hp₁ i).le))
    (bernoulliMass_logconcave p hp (fun i => (hp₁ i).le))
    (fun k hk => bernoulliMass_neg p k hk)
    (fun k hk => bernoulliMass_eq_zero_above p k hk)
  rw [← Int.natCast_zero, bernoulliMass_natCast,
    coeff_bernoulliPolynomial_pos_iff p hp hp₁]
  exact Nat.zero_le _

/-- Scalar differentiation of one actual convolution edge at the fair value. -/
theorem hasDerivAt_fair_edge (q a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    HasDerivAt (fun t : ℝ =>
      ((1 - t) * b + t * a - ((1 - t) * c + t * b)) *
        ((1 - t) * b + t * a + ((1 - t) * c + t * b)) ^ (q - 1))
      (-2 * fairLocalTerm q a b c) (1 / 2) := by
  by_cases hz : a + 2 * b + c = 0
  · have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    have hc0 : c = 0 := by linarith
    simp only [ha0, hb0, hc0, mul_zero, add_zero, sub_self, zero_mul, fairLocalTerm,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div]
    exact hasDerivAt_const _ _
  have hA : 0 < (a + 2 * b + c) / 2 := by have := lt_of_le_of_ne (by linarith : 0 ≤ a + 2 * b + c) (Ne.symm hz); linarith
  have hd (d e : ℝ) : HasDerivAt (fun t : ℝ => (1 - t) * d + t * e) (e - d) (1 / 2) := by
    convert (((hasDerivAt_const (1 / 2) (1 : ℝ)).sub (hasDerivAt_id (1 / 2))).mul_const d).add
      ((hasDerivAt_id (1 / 2)).mul_const e) using 1
    · funext t
      simp only [Pi.add_apply, Pi.sub_apply, id_eq]
    · simp
      ring
  have hav : (1 - (1 / 2 : ℝ)) * b + 1 / 2 * a +
      ((1 - 1 / 2) * c + 1 / 2 * b) = (a + 2 * b + c) / 2 := by ring
  have ht := ((hd b a).sub (hd c b)).mul
    (((hd b a).add (hd c b)).rpow_const (p := q - 1) (Or.inl (by
      simp only [Pi.add_apply]
      rw [hav]
      exact hA.ne')))
  convert ht using 1
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [hav, show q - 1 - 1 = q - 2 by ring]
  have hp : ((a + 2 * b + c) / 2) ^ (q - 1) =
      ((a + 2 * b + c) / 2) ^ (q - 2) * ((a + 2 * b + c) / 2) := by
    rw [← Real.rpow_add_one hA.ne']
    congr 1
    ring
  rw [hp]
  unfold fairLocalTerm
  ring

/-- Exact derivative of the actual midpoint functional in a fair coordinate. -/
theorem hasDerivAt_midpointFunctional_cons_half {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hp₁ : ∀ i, p i ≤ 1) :
    HasDerivAt (fun t : ℝ => midpointFunctional q (Fin.cons t p))
      (-2 * ∑ k : Fin (n + 3), fairLocalTerm q (bernoulliMass p ((k.val : ℤ) - 2))
        (bernoulliMass p ((k.val : ℤ) - 1)) (bernoulliMass p (k.val : ℤ))) (1 / 2) := by
  have ht := HasDerivAt.fun_sum (u := Finset.univ)
    (fun k (_ : k ∈ (Finset.univ : Finset (Fin (n + 3)))) =>
      hasDerivAt_fair_edge q (bernoulliMass p ((k.val : ℤ) - 2))
        (bernoulliMass p ((k.val : ℤ) - 1)) (bernoulliMass p (k.val : ℤ))
        (bernoulliMass_nonneg p hp hp₁ _) (bernoulliMass_nonneg p hp hp₁ _)
        (bernoulliMass_nonneg p hp hp₁ _))
  convert ht using 1
  · funext t
    unfold midpointFunctional edgeDifference edgeSum
    simp only [bernoulliMass_cons, sub_sub, show (1 : ℤ) + 1 = 2 by omega]
  · rw [Finset.mul_sum]

/-- Strictly negative fair-coordinate derivative for every order strictly
between zero and one. The background may contain zero coins. -/
theorem deriv_midpointFunctional_cons_half_neg {n : ℕ} (q : ℝ) (p : Fin n → ℝ)
    (hq₀ : 0 < q) (hq₁ : q < 1) (hp : ∀ i, 0 ≤ p i) (hp₁ : ∀ i, p i < 1) :
    deriv (fun t : ℝ => midpointFunctional q (Fin.cons t p)) (1 / 2) < 0 := by
  rw [(hasDerivAt_midpointFunctional_cons_half q p hp (fun i => (hp₁ i).le)).deriv]
  exact mul_neg_of_neg_of_pos (by norm_num) (sum_fairLocalTerm_bernoulli_pos q p hq₀ hq₁ hp hp₁)

/-- The strict fair derivative applies to any named coordinate of the original
coin vector, independently of the ordering of the remaining coins. -/
theorem deriv_midpointFunctional_update_half_neg {n : ℕ} (q : ℝ)
    (p : Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (hq₀ : 0 < q) (hq₁ : q < 1)
    (hp : ∀ j, j ≠ i → 0 ≤ p j) (hp₁ : ∀ j, j ≠ i → p j < 1) :
    deriv (fun t : ℝ => midpointFunctional q (Function.update p i t)) (1 / 2) < 0 := by
  have he : (fun t : ℝ => midpointFunctional q (Function.update p i t)) =
      (fun t : ℝ => midpointFunctional q (Fin.cons t (omitCoin p i))) := by
    funext t
    unfold midpointFunctional edgeDifference edgeSum bernoulliMass
    rw [bernoulliPolynomial_update_eq_cons]
  rw [he]
  exact deriv_midpointFunctional_cons_half_neg q (omitCoin p i) hq₀ hq₁
    (fun j => hp (i.succAbove j) (Fin.succAbove_ne i j))
    (fun j => hp₁ (i.succAbove j) (Fin.succAbove_ne i j))

end RenyiMonotonicity
