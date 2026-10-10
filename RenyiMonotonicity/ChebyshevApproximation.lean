module

public import RenyiMonotonicity.BetaBinomialIdentities
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Topology.Algebra.Order.Field

@[expose] public section

open Polynomial Filter
open scoped Topology

namespace RenyiMonotonicity

/-- Coefficients under a linear change fixing the origin. -/
theorem coeff_comp_C_mul_X (P : ℝ[X]) (c : ℝ) (k : ℕ) :
    (P.comp (C c * X)).coeff k = P.coeff k * c ^ k := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp [hP, hQ, add_mul]
  | monomial n a =>
    simp only [monomial_comp, mul_pow, ← C_pow, coeff_C_mul,
      coeff_X_pow, coeff_monomial]
    split_ifs with h <;> simp_all

/-- Taylor coefficients and ordinary derivatives, with the factorial explicit. -/
theorem factorial_mul_taylor_coeff (P : ℝ[X]) (k : ℕ) (x : ℝ) :
    (k.factorial : ℝ) * (taylor x P).coeff k = (derivative^[k] P).eval x := by
  rw [taylor_coeff, ← factorial_smul_hasseDeriv]
  simp

/-- A finite polynomial approximation to `cosh (d * sqrt z)`. -/
noncomputable def chebyshevApproximation (L d : ℕ) : ℝ[X] :=
  (taylor 1 (Chebyshev.T ℝ (d * L : ℕ))).comp (C (1 / (2 * (L : ℝ)^2)) * X)

theorem chebyshevApproximation_eval (L d : ℕ) (z : ℝ) :
    (chebyshevApproximation L d).eval z =
      (Chebyshev.T ℝ (d * L : ℕ)).eval (1 + z / (2 * (L : ℝ)^2)) := by
  simp only [chebyshevApproximation, eval_comp, taylor_eval, eval_mul, eval_C, eval_X]
  congr 1
  ring

theorem chebyshevApproximation_coeff_zero (L d : ℕ) :
    (chebyshevApproximation L d).coeff 0 = 1 := by
  rw [chebyshevApproximation, coeff_comp_C_mul_X, taylor_coeff_zero]
  simp

/-- Exact coefficient recurrence inherited from the Chebyshev differential equation. -/
theorem chebyshevApproximation_coeff_step (L d k : ℕ) (hL : L ≠ 0) :
    (2 * (k : ℝ) + 1) * (k + 1) * (chebyshevApproximation L d).coeff (k + 1) =
      (((d : ℝ)^2 - (k : ℝ)^2 / (L : ℝ)^2) / 2) *
        (chebyshevApproximation L d).coeff k := by
  have hLn : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL
  have hf : (k.factorial : ℝ) ≠ 0 := by positivity
  have h := Chebyshev.iterate_derivative_T_eval_one_recurrence (R := ℝ) (d * L : ℕ) k
  rw [← factorial_mul_taylor_coeff, ← factorial_mul_taylor_coeff] at h
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
  push_cast at h
  simp only [chebyshevApproximation, coeff_comp_C_mul_X, pow_succ]
  field_simp
  field_simp at h
  simp only [Nat.cast_mul]
  nlinarith [h]

/-- Every fixed coefficient converges, using the exact finite differential recurrence. -/
theorem tendsto_chebyshevApproximation_coeff (d k : ℕ) :
    Tendsto (fun L : ℕ => (chebyshevApproximation L d).coeff k) atTop
      (𝓝 ((d : ℝ)^(2*k) / ((2*k).factorial : ℝ))) := by
  induction k with
  | zero => simpa only [chebyshevApproximation_coeff_zero, mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  | succ k ih =>
    have hz : Tendsto (fun L : ℕ => (L : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hq : Tendsto (fun L : ℕ => (((d : ℝ)^2 - (k : ℝ)^2 / (L : ℝ)^2) / 2))
        atTop (𝓝 ((d : ℝ)^2 / 2)) := by
      simpa [div_eq_mul_inv, inv_pow] using
        ((tendsto_const_nhds.sub (tendsto_const_nhds.mul (hz.pow 2))).div_const 2)
    have hden : (2 * (k : ℝ) + 1) * (k + 1) ≠ 0 := by positivity
    have H := (hq.mul ih).div_const ((2 * (k : ℝ) + 1) * (k + 1))
    have he : ∀ᶠ L : ℕ in atTop,
        (chebyshevApproximation L d).coeff (k + 1) =
          ((((d : ℝ)^2 - (k : ℝ)^2 / (L : ℝ)^2) / 2) *
            (chebyshevApproximation L d).coeff k) / ((2 * (k : ℝ) + 1) * (k + 1)) := by
      filter_upwards [eventually_ge_atTop 1] with L hL
      exact (eq_div_iff hden).mpr (by
        simpa only [mul_comm (chebyshevApproximation L d |>.coeff (k + 1))] using
          chebyshevApproximation_coeff_step L d k (by omega))
    have hlim : (d : ℝ)^2 / 2 * ((d : ℝ)^(2*k) / ((2*k).factorial : ℝ)) /
        ((2 * (k : ℝ) + 1) * (k + 1)) = (d : ℝ)^(2*(k+1)) / ((2*(k+1)).factorial : ℝ) := by
      rw [show 2*(k+1)=2*k+1+1 by omega, Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      rw [pow_succ, pow_succ]
      field_simp
      ring
    rw [hlim] at H
    apply H.congr'
    filter_upwards [he] with L hL using hL.symm

end RenyiMonotonicity
