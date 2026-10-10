module

public import RenyiMonotonicity.ChebyshevApproximation
public import Mathlib.Analysis.SpecialFunctions.Arcosh

@[expose] public section

open Polynomial Filter
open scoped Topology BigOperators

namespace RenyiMonotonicity

/-- Apply the finite Chebyshev approximation to a polynomial in `cosh t`. -/
noncomputable def polynomialChebyshevApproximation (P : ℝ[X]) (L : ℕ) : ℝ[X] :=
  (taylor 1 (P.comp (Chebyshev.T ℝ (L : ℤ)))).comp
    (C (1 / (2 * (L : ℝ)^2)) * X)

/-- The ordinary Gegenbauer polynomial is the actual symmetric finite
beta-binomial sum of Chebyshev polynomials. -/
theorem gegenbauerPolynomial_eq_chebyshev_sum (a : ℝ) (ha : 0 < a) (N : ℕ) :
    gegenbauerPolynomial a N = ∑ k ∈ Finset.range (N + 1),
      C (betaBinomialWeight a N k) * Chebyshev.T ℝ ((N : ℤ) - 2 * k) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ici_infinite (1 : ℝ)).mono
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Real.cosh_surjOn hx
  simp only [Set.mem_ofPred_eq, eval_finsetSum, eval_mul, eval_C, Chebyshev.T_real_cosh]
  have hp := betaBinomialMGF_eq_sum a N t
  have hm := betaBinomialMGF_eq_sum a N (-t)
  rw [betaBinomialMGF_eq_gegenbauer a ha] at hp hm
  rw [Real.cosh_neg] at hm
  have he : (∑ k ∈ Finset.range (N + 1), betaBinomialWeight a N k *
      Real.cosh (((N : ℤ) - 2*k : ℤ) * t)) =
      ((∑ k ∈ Finset.range (N + 1), betaBinomialWeight a N k * Real.exp (((N : ℝ)-2*k)*t)) +
       (∑ k ∈ Finset.range (N + 1), betaBinomialWeight a N k * Real.exp (((N : ℝ)-2*k)*(-t)))) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Real.cosh_eq]
    push_cast
    rw [show -(((N : ℝ)-2*k)*t)=((N : ℝ)-2*k)*(-t) by ring]
    ring
  rw [he, ← hp, ← hm]
  ring

/-- Chebyshev composition multiplies its integer frequency. -/
theorem polynomialChebyshevApproximation_T (L : ℕ) (d : ℤ) :
    polynomialChebyshevApproximation (Chebyshev.T ℝ d) L =
      chebyshevApproximation L d.natAbs := by
  rw [polynomialChebyshevApproximation, ← Chebyshev.T_mul]
  have he : Chebyshev.T ℝ (d * (L : ℤ)) = Chebyshev.T ℝ (d.natAbs * L : ℕ) := by
    rw [← Chebyshev.T_natAbs, Int.natAbs_mul, Int.natAbs_natCast]
  rw [he]
  rfl

theorem polynomialChebyshevApproximation_sum (P : ℕ → ℝ[X]) (n L : ℕ) :
    polynomialChebyshevApproximation (∑ k ∈ Finset.range n, P k) L =
      ∑ k ∈ Finset.range n, polynomialChebyshevApproximation (P k) L := by
  simp [polynomialChebyshevApproximation, sum_comp, map_sum]

theorem polynomialChebyshevApproximation_C_mul (P : ℝ[X]) (c : ℝ) (L : ℕ) :
    polynomialChebyshevApproximation (C c * P) L =
      C c * polynomialChebyshevApproximation P L := by
  simp [polynomialChebyshevApproximation, mul_comp, taylor_mul]

/-- Exact finite approximation of the symmetric mass law. -/
theorem polynomialChebyshevApproximation_gegenbauer (a : ℝ) (ha : 0 < a) (N L : ℕ) :
    polynomialChebyshevApproximation (gegenbauerPolynomial a N) L =
      ∑ k ∈ Finset.range (N + 1), C (betaBinomialWeight a N k) *
        chebyshevApproximation L (((N : ℤ)-2*k).natAbs) := by
  rw [gegenbauerPolynomial_eq_chebyshev_sum a ha N, polynomialChebyshevApproximation_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [polynomialChebyshevApproximation_C_mul, polynomialChebyshevApproximation_T]

/-- Even moments appear as the exact coefficient limits, including central zero masses. -/
theorem tendsto_polynomialChebyshevApproximation_gegenbauer_coeff
    (a : ℝ) (ha : 0 < a) (N ell : ℕ) :
    Tendsto (fun L : ℕ => (polynomialChebyshevApproximation (gegenbauerPolynomial a N) L).coeff ell)
      atTop (𝓝 ((∑ k ∈ Finset.range (N+1), betaBinomialWeight a N k *
        ((N : ℝ)-2*k)^(2*ell)) / ((2*ell).factorial : ℝ))) := by
  simp only [polynomialChebyshevApproximation_gegenbauer a ha, finsetSum_coeff, coeff_C_mul]
  have H := tendsto_finsetSum (Finset.range (N+1)) (fun k hk =>
    (tendsto_chebyshevApproximation_coeff (((N : ℤ)-2*k).natAbs) ell).const_mul
      (betaBinomialWeight a N k))
  convert H using 1
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have he : ((((N : ℤ)-2*k).natAbs : ℕ) : ℝ)^(2*ell) = ((N : ℝ)-2*k)^(2*ell) := by
    rw [Nat.cast_natAbs, Int.cast_abs, pow_mul, sq_abs]
    push_cast
    rw [pow_mul]
  rw [he]
  ring

end RenyiMonotonicity
