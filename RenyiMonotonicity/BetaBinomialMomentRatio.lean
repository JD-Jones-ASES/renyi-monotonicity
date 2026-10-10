module

public import RenyiMonotonicity.BetaBinomialMomentLimit
public import RenyiMonotonicity.ChebyshevRootComparison

@[expose] public section

open Polynomial Filter
open scoped Topology

namespace RenyiMonotonicity

/-- The finite `F` approximant is the actual Gegenbauer/Chebyshev polynomial,
with its positive normalization retained. -/
theorem betaBinomialFApproximation_factor (a : ℝ) (m L : ℕ) :
    betaBinomialFApproximation a m L = C (4*a^2 * gegenbauerScale (a+1) m) *
      chebyshevGegenbauerF (a+1) m L := by
  rw [betaBinomialFApproximation, polynomialChebyshevApproximation_eq_comp]
  simp only [gegenbauerPolynomial, mul_comp, C_comp, chebyshevGegenbauerF, chebyshevAffine, map_mul]
  ring

/-- The finite `G` approximant has the sine factor and the adjacent Gegenbauer degree. -/
theorem betaBinomialGApproximation_factor (a : ℝ) (ha : 0<a) (m L : ℕ) (hL : 0<L) :
    betaBinomialGApproximation a (m+2) L =
      C (2*a/(L:ℝ) * gegenbauerScale (a+1) (m+1)) * chebyshevGegenbauerG (a+1) m L := by
  rw [betaBinomialGApproximation, show m+2=(m+1)+1 by omega,
    betaBinomial_derivativeApproximation_factor a ha (m+1) L hL]
  simp only [gegenbauerPolynomial, mul_comp, C_comp, chebyshevGegenbauerG, chebyshevAffine, map_mul]
  ring

/-- The genuine finite approximations satisfy the cross inequality by their complete
ordered negative roots. -/
theorem betaBinomialApproximation_cross_nonneg (a : ℝ) (ha : 0<a) (m : ℕ) (hm : 0 < m)
    (L : ℕ) (hL : 0<L) (ell : ℕ) (hell : ell < (m+2)*L-1) :
    (betaBinomialFApproximation a m L).coeff (ell+1) * (betaBinomialGApproximation a (m+2) L).coeff ell ≤
      (betaBinomialFApproximation a m L).coeff ell * (betaBinomialGApproximation a (m+2) L).coeff (ell+1) := by
  have H := chebyshevGegenbauer_cross_nonneg (a+1) (by linarith) m hm L hL ell hell
  have hc : 0 ≤ (4*a^2 * gegenbauerScale (a+1) m) *
      (2*a/(L:ℝ) * gegenbauerScale (a+1) (m+1)) := by
    have hp := gegenbauerScale_pos (a+1) (by linarith) m
    have hq := gegenbauerScale_pos (a+1) (by linarith) (m+1)
    positivity
  have HH := mul_le_mul_of_nonneg_left H hc
  rw [betaBinomialFApproximation_factor, betaBinomialGApproximation_factor a ha m L hL]
  simp only [coeff_C_mul]
  convert HH using 1 <;> ring

/-- The actual beta-binomial moment ratios are decreasing, for every moment index.
The finite root argument and coefficient convergence discharge all structural premises. -/
theorem betaBinomialMoment_ratio_antitone_step (N : ℕ) (hN : 3≤N) (a : ℝ) (ha : 1<a)
    (ell : ℕ) :
    (2*((ell+1:ℕ):ℝ)+1) * (betaBinomialMoment N a (ell+1) / betaBinomialMoment N a (ell+2) - 1) ≤
      (2*(ell:ℝ)+1) * (betaBinomialMoment N a ell / betaBinomialMoment N a (ell+1) - 1) := by
  let m := N-2
  have hm : 0 < m := by dsimp [m]; omega
  have he : N=m+2 := by dsimp [m]; omega
  rw [he]
  apply betaBinomialMoment_ratio_of_approximation a (by linarith) m ell
  filter_upwards [eventually_ge_atTop (ell+1)] with L hL
  have hLp : 0<L := by omega
  apply betaBinomialApproximation_cross_nonneg a (by linarith) m hm L hLp ell
  have hmul : 3*L ≤ (m+2)*L := Nat.mul_le_mul_right L (by omega)
  omega

end RenyiMonotonicity
