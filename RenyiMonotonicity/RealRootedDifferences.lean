module
public import RenyiMonotonicity.CoordinateLaw
public import Mathlib.Analysis.Complex.Polynomial.GaussLucas

@[expose] public section

noncomputable section
open Polynomial Set

namespace RenyiMonotonicity

/-- A real split polynomial has a real split derivative, by Gauss--Lucas. -/
theorem splits_derivative_real (P : ℝ[X]) (hP : P.Splits) : P.derivative.Splits := by
  by_cases hdeg : 0 < P.degree
  · apply Polynomial.Splits.of_splits_map Complex.ofRealHom (IsAlgClosed.splits _)
    intro z hz
    let Q := P.map Complex.ofRealHom
    have hz' : z ∈ Q.derivative.rootSet ℂ := by
      rw [mem_rootSet, coe_aeval_eq_eval]
      have hh := (mem_roots (by
        intro he
        simp [he] at hz)).mp hz
      simpa only [Q, Polynomial.derivative_map] using ⟨by
        intro he
        simp [he] at hz, hh⟩
    have hQdeg : 0 < Q.degree := by simpa only [Q, degree_map] using hdeg
    have hc : Convex ℝ {w : ℂ | w.im = 0} := by
      intro u hu v hv a b _ _ _
      change u.im = 0 at hu
      change v.im = 0 at hv
      change (a • u + b • v).im = 0
      simp only [Complex.add_im, Complex.smul_im, hu, hv, smul_zero, zero_add]
    have hroots : Q.rootSet ℂ ⊆ {w : ℂ | w.im = 0} := by
      intro w hw
      have hw' := (mem_rootSet.mp hw).2
      rw [coe_aeval_eq_eval] at hw'
      have hPn : P ≠ 0 := by intro he; simp [he] at hdeg
      obtain ⟨r, hr⟩ := hP.mem_range_of_isRoot hPn (show Q.IsRoot w from hw')
      change (r : ℂ) = w at hr
      simp [← hr]
    have him : z.im = 0 :=
      (convexHull_min hroots hc) (rootSet_derivative_subset_convexHull_rootSet hQdeg hz')
    exact ⟨z.re, Complex.ext (by simp) (by simpa using him.symm)⟩
  · have hd : P.degree ≤ 0 := le_of_not_gt hdeg
    have he : P = C (P.coeff 0) := eq_C_of_degree_le_zero hd
    rw [he, derivative_C]
    exact Polynomial.Splits.zero

/-- Laguerre's elementary quadratic expression is nonnegative for every real
split polynomial. The product rule proves this directly from the linear factors. -/
theorem laguerre_nonneg_of_splits (P : ℝ[X]) (hP : P.Splits) (x : ℝ) :
    0 ≤ P.derivative.eval x ^ 2 - P.eval x * P.derivative.derivative.eval x := by
  induction hP using Submonoid.closure_induction with
  | mem f hf =>
      rcases hf with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> simp
  | one => simp
  | mul f g hf hg ihf ihg =>
      have h1 := mul_nonneg (sq_nonneg (g.eval x)) ihf
      have h2 := mul_nonneg (sq_nonneg (f.eval x)) ihg
      simp only [derivative_mul, derivative_add, eval_mul, eval_add]
      nlinarith

theorem splits_iterate_derivative_real (P : ℝ[X]) (hP : P.Splits) (k : ℕ) :
    ((derivative^[k]) P).Splits := by
  induction k with
  | zero => exact hP
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact splits_derivative_real _ ih

theorem eval_zero_iterate_derivative (P : ℝ[X]) (k : ℕ) :
    ((derivative^[k]) P).eval 0 = (k.factorial : ℝ) * P.coeff k := by
  rw [← coeff_zero_eq_eval_zero, coeff_iterate_derivative]
  simp only [zero_add, Nat.descFactorial_self, nsmul_eq_mul]

/-- Newton's local coefficient inequality without a sign assumption on the
other coefficients. All roots of the polynomial are real. -/
theorem newton_coefficient_inequality (P : ℝ[X]) (hP : P.Splits) (k : ℕ) :
    ((k : ℝ) + 2) * P.coeff k * P.coeff (k + 2) ≤
      ((k : ℝ) + 1) * P.coeff (k + 1) ^ 2 := by
  have h := laguerre_nonneg_of_splits ((derivative^[k]) P)
    (splits_iterate_derivative_real P hP k) 0
  have h1 : derivative ((derivative^[k]) P) = (derivative^[k + 1]) P :=
    (Function.iterate_succ_apply' derivative k P).symm
  have h2 : derivative (derivative ((derivative^[k]) P)) = (derivative^[k + 2]) P := by
    rw [h1]
    exact (Function.iterate_succ_apply' derivative (k + 1) P).symm
  rw [h2, h1, eval_zero_iterate_derivative, eval_zero_iterate_derivative,
    eval_zero_iterate_derivative] at h
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
  have hf : 0 < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have hid : (((k : ℝ) + 1) * k.factorial * P.coeff (k + 1)) ^ 2 -
      (k.factorial * P.coeff k) *
        (((k : ℝ) + 2) * (((k : ℝ) + 1) * k.factorial) * P.coeff (k + 2)) =
      (k.factorial ^ 2 * ((k : ℝ) + 1)) *
        (((k : ℝ) + 1) * P.coeff (k + 1) ^ 2 -
          ((k : ℝ) + 2) * P.coeff k * P.coeff (k + 2)) := by ring
  have hh : 0 ≤ (k.factorial ^ 2 * ((k : ℝ) + 1)) *
      (((k : ℝ) + 1) * P.coeff (k + 1) ^ 2 -
        ((k : ℝ) + 2) * P.coeff k * P.coeff (k + 2)) := by
    rw [← hid]
    convert h using 1
    ring
  have hp : 0 < k.factorial ^ 2 * ((k : ℝ) + 1) := by positivity
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hp).mp hh)

/-- Every nonzero middle coefficient of a real split polynomial gives strict
unnormalized log-concavity, even when the polynomial has roots of both signs. -/
theorem strict_logconcave_coeff_of_splits (P : ℝ[X]) (hP : P.Splits) (k : ℕ)
    (hk : P.coeff (k + 1) ≠ 0) :
    P.coeff k * P.coeff (k + 2) < P.coeff (k + 1) ^ 2 := by
  have hn := newton_coefficient_inequality P hP k
  have hs := sq_pos_of_ne_zero hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

theorem bernoulliPolynomial_splits {n : ℕ} (p : Fin n → ℝ) :
    (bernoulliPolynomial p).Splits := by
  apply Polynomial.Splits.prod
  intro i _
  apply Polynomial.Splits.of_natDegree_le_one
  compute_degree

theorem firstDifferencePolynomial_splits {n : ℕ} (p : Fin n → ℝ) :
    (((1 : ℝ[X]) - X) * bernoulliPolynomial p).Splits := by
  apply Polynomial.Splits.mul _ (bernoulliPolynomial_splits p)
  apply Polynomial.Splits.of_natDegree_le_one
  compute_degree

theorem coeff_firstDifferencePolynomial {n : ℕ} (p : Fin n → ℝ) (k : ℕ) :
    (((1 : ℝ[X]) - X) * bernoulliPolynomial p).coeff k =
      bernoulliMass p (k : ℤ) - bernoulliMass p ((k : ℤ) - 1) := by
  cases k with
  | zero => simp [sub_mul, bernoulliMass]
  | succ k =>
      rw [show ((k.succ : ℕ) : ℤ) - 1 = (k : ℤ) by omega]
      simp only [sub_mul, one_mul, coeff_sub, coeff_X_mul,
        bernoulliMass_natCast]

/-- Strict log-concavity of the nonzero first-difference branch of the actual
Bernoulli coefficient sequence, including the initial zero-extension edge. -/
theorem bernoulli_firstDifference_strict_logconcave {n : ℕ} (p : Fin n → ℝ)
    (k : ℤ) (hk : 0 ≤ k)
    (hmid : bernoulliMass p (k + 1) - bernoulliMass p k ≠ 0) :
    (bernoulliMass p k - bernoulliMass p (k - 1)) *
      (bernoulliMass p (k + 2) - bernoulliMass p (k + 1)) <
      (bernoulliMass p (k + 1) - bernoulliMass p k) ^ 2 := by
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hk
  have hcoeff : (((1 : ℝ[X]) - X) * bernoulliPolynomial p).coeff (j + 1) ≠ 0 := by
    simpa [coeff_firstDifferencePolynomial, Nat.cast_add, Nat.cast_one] using hmid
  have hh := strict_logconcave_coeff_of_splits _ (firstDifferencePolynomial_splits p) j hcoeff
  simpa [coeff_firstDifferencePolynomial, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
    show (j : ℤ) + 2 - 1 = (j : ℤ) + 1 by ring] using hh

end RenyiMonotonicity
