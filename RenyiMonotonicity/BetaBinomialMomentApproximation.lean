module

public import RenyiMonotonicity.BetaBinomialApproximation
public import RenyiMonotonicity.CMBDefinitions

@[expose] public section

open Polynomial Filter
open scoped Topology BigOperators

namespace RenyiMonotonicity

theorem polynomialChebyshevApproximation_eq_comp (P : ℝ[X]) (L : ℕ) :
    polynomialChebyshevApproximation P L =
      P.comp ((Chebyshev.T ℝ (L : ℤ)).comp (C 1 + C (1/(2*(L:ℝ)^2))*X)) := by
  simp only [polynomialChebyshevApproximation, taylor_apply, comp_assoc, add_comp, X_comp, C_comp]
  congr 2
  ring

/-- Unscaled even moments on the integer grid. -/
noncomputable def betaBinomialRawMoment (a : ℝ) (N ell : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N+1), betaBinomialWeight a N k * ((N : ℝ)-2*k)^(2*ell)

/-- Removing the two endpoint terms gives the exact shifted-shape moment identity. -/
theorem betaBinomialRawMoment_shift (a : ℝ) (n ell : ℕ) :
    ((n+2 : ℕ) : ℝ)^2 * betaBinomialRawMoment a (n+2) ell -
      betaBinomialRawMoment a (n+2) (ell+1) =
        4*a^2 * betaBinomialRawMoment (a+1) n ell := by
  have he : ((n+2 : ℕ) : ℝ)^2 * betaBinomialRawMoment a (n+2) ell -
      betaBinomialRawMoment a (n+2) (ell+1) =
      ∑ k ∈ Finset.range (n+2+1), (((n+2 : ℕ) : ℝ)^2 - (((n+2 : ℕ) : ℝ)-2*k)^2) *
        betaBinomialWeight a (n+2) k * (((n+2 : ℕ) : ℝ)-2*k)^(2*ell) := by
    simp only [betaBinomialRawMoment, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [show 2*(ell+1)=2*ell+2 by omega, pow_add]
    ring
  rw [he, betaBinomialRawMoment, Finset.mul_sum,
    Finset.sum_range_succ', Finset.sum_range_succ]
  simp only [Nat.cast_zero, mul_zero, sub_zero, sub_self, zero_mul, add_zero]
  have hlast : ((n + 2 : ℝ)^2 - ((n+2 : ℝ)-2*(n+2))^2)=0 := by ring
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  rw [show (n+1 : ℝ)+1=n+2 by ring, hlast, zero_mul, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa using Finset.mem_range.mp hk
  have H := betaBinomialWeight_quadratic_shift a n k hk'
  have he : (n+2 : ℝ)-2*(k+1)=n-2*k := by ring
  rw [he, H]
  ring

/-- The scaled-grid moment in the final CMB contract. -/
theorem betaBinomialRawMoment_eq_scaled (a : ℝ) (N ell : ℕ) (hN : N ≠ 0) :
    betaBinomialRawMoment a N ell = (N : ℝ)^(2*ell) * betaBinomialMoment N a ell := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [betaBinomialRawMoment, betaBinomialMoment, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [cmbGrid, ← pow_mul, div_pow]
  field_simp

/-- The standard Gegenbauer derivative identity follows from the actual finite law. -/
theorem derivative_gegenbauerPolynomial (a : ℝ) (ha : 0<a) (n : ℕ) :
    derivative (gegenbauerPolynomial a (n+1)) = C (2*a) * gegenbauerPolynomial (a+1) n := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioi_infinite (1 : ℝ)).mono
  intro x hx
  have hx' : 1 ≤ x := le_of_lt hx
  obtain ⟨t, ht, rfl⟩ := Real.cosh_surjOn hx'
  have ht0 : t ≠ 0 := by intro h; simp [h] at hx
  have hs : Real.sinh t ≠ 0 := Real.sinh_ne_zero.mpr ht0
  have H := ((gegenbauerPolynomial a (n+1)).hasDerivAt (Real.cosh t)).comp t (Real.hasDerivAt_cosh t)
  have hfun : (fun u => (gegenbauerPolynomial a (n+1)).eval (Real.cosh u)) = betaBinomialMGF a (n+1) := by
    funext u
    exact (betaBinomialMGF_eq_gegenbauer a ha (n+1) u).symm
  simp only [Function.comp_def] at H
  rw [hfun] at H
  have he := H.unique (hasDerivAt_betaBinomialMGF_shift a n t)
  rw [betaBinomialMGF_eq_gegenbauer _ (by linarith)] at he
  simp only [Set.mem_ofPred_eq, eval_mul, eval_C]
  apply (mul_right_cancel₀ hs)
  nlinarith [he]

/-- Coefficients of the derivative approximation converge to the odd factorial normalization. -/
theorem tendsto_betaBinomial_derivativeApproximation_coeff (a : ℝ) (ha : 0<a) (N ell : ℕ) :
    Tendsto (fun L : ℕ => (C (2 : ℝ) * derivative
      (polynomialChebyshevApproximation (gegenbauerPolynomial a N) L)).coeff ell)
      atTop (𝓝 (betaBinomialRawMoment a N (ell+1) / ((2*ell+1).factorial : ℝ))) := by
  simp only [coeff_C_mul, coeff_derivative]
  have H := ((tendsto_polynomialChebyshevApproximation_gegenbauer_coeff a ha N (ell+1)).mul_const
    ((ell : ℝ)+1)).const_mul 2
  convert H using 1
  congr 1
  change betaBinomialRawMoment a N (ell+1) / ((2*ell+1).factorial : ℝ) =
    2 * (betaBinomialRawMoment a N (ell+1) / ((2*(ell+1)).factorial : ℝ) * ((ell:ℝ)+1))
  have hf : ((2*(ell+1)).factorial : ℝ) = (2*(ell:ℝ)+2) * ((2*ell+1).factorial : ℝ) := by
    rw [show 2*(ell+1)=2*ell+1+1 by omega, Nat.factorial_succ]
    push_cast
    ring
  rw [hf]
  field_simp

/-- The finite derivative approximant has exactly the `U` and Gegenbauer factors. -/
theorem betaBinomial_derivativeApproximation_factor (a : ℝ) (ha : 0<a) (n L : ℕ) (hL : 0<L) :
    C (2 : ℝ) * derivative (polynomialChebyshevApproximation (gegenbauerPolynomial a (n+1)) L) =
      C (2*a/(L:ℝ)) *
        ((Chebyshev.U ℝ ((L-1:ℕ):ℤ)).comp (C 1 + C (1/(2*(L:ℝ)^2))*X)) *
        (gegenbauerPolynomial (a+1) n).comp
          ((Chebyshev.T ℝ (L:ℤ)).comp (C 1 + C (1/(2*(L:ℝ)^2))*X)) := by
  have hn : (L : ℝ) ≠ 0 := by positivity
  have hcast : ((L-1:ℕ):ℤ)=(L:ℤ)-1 := by omega
  rw [polynomialChebyshevApproximation_eq_comp, derivative_comp,
    derivative_comp, derivative_gegenbauerPolynomial a ha,
    Chebyshev.T_derivative_eq_U, ← hcast]
  simp only [derivative_add, derivative_C, derivative_mul, derivative_X,
    zero_mul, zero_add, mul_one, mul_comp, C_comp]
  simp only [Int.cast_natCast]
  rw [show (L : ℝ[X]) = C (L : ℝ) by simp, C_comp]
  have hc : (2 : ℝ)*(1/(2*(L:ℝ)^2))*(L:ℝ)*(2*a)=2*a/(L:ℝ) := by field_simp
  calc
    _ = C ((2 : ℝ)*(1/(2*(L:ℝ)^2))*(L:ℝ)*(2*a)) *
        ((Chebyshev.U ℝ ((L-1:ℕ):ℤ)).comp (C 1+C (1/(2*(L:ℝ)^2))*X)) *
        (gegenbauerPolynomial (a+1) n).comp
          ((Chebyshev.T ℝ (L:ℤ)).comp (C 1+C (1/(2*(L:ℝ)^2))*X)) := by
            simp only [map_mul]
            ring
    _ = _ := by rw [hc]

end RenyiMonotonicity
