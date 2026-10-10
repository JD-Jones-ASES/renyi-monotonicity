module

public import RenyiMonotonicity.BetaBinomialMomentApproximation

@[expose] public section

open Polynomial Filter
open scoped Topology BigOperators

namespace RenyiMonotonicity

noncomputable def betaBinomialFApproximation (a : ℝ) (m L : ℕ) : ℝ[X] :=
  C (4*a^2) * polynomialChebyshevApproximation (gegenbauerPolynomial (a+1) m) L

noncomputable def betaBinomialGApproximation (a : ℝ) (N L : ℕ) : ℝ[X] :=
  C 2 * derivative (polynomialChebyshevApproximation (gegenbauerPolynomial a N) L)

noncomputable def betaBinomialFCoefficient (a : ℝ) (N ell : ℕ) : ℝ :=
  ((N:ℝ)^2 * betaBinomialRawMoment a N ell - betaBinomialRawMoment a N (ell+1)) /
    ((2*ell).factorial : ℝ)

noncomputable def betaBinomialGCoefficient (a : ℝ) (N ell : ℕ) : ℝ :=
  betaBinomialRawMoment a N (ell+1) / ((2*ell+1).factorial : ℝ)

theorem betaBinomialRawMoment_pos (a : ℝ) (ha : 0<a) (N ell : ℕ) (hN : N ≠ 0) :
    0 < betaBinomialRawMoment a N ell := by
  rw [betaBinomialRawMoment_eq_scaled a N ell hN]
  exact mul_pos (pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hN) _)
    (betaBinomialMoment_pos N hN a ha ell)

theorem betaBinomialGCoefficient_pos (a : ℝ) (ha : 0<a) (N ell : ℕ) (hN : N ≠ 0) :
    0 < betaBinomialGCoefficient a N ell :=
  div_pos (betaBinomialRawMoment_pos a ha N (ell+1) hN) (by positivity)

theorem tendsto_betaBinomialFApproximation_coeff (a : ℝ) (ha : 0<a) (m ell : ℕ) :
    Tendsto (fun L : ℕ => (betaBinomialFApproximation a m L).coeff ell)
      atTop (𝓝 (betaBinomialFCoefficient a (m+2) ell)) := by
  have H := (tendsto_polynomialChebyshevApproximation_gegenbauer_coeff (a+1) (by linarith) m ell).const_mul
    (4*a^2)
  simp only [betaBinomialFApproximation, coeff_C_mul]
  convert H using 1
  congr 1
  rw [betaBinomialFCoefficient, betaBinomialRawMoment_shift]
  dsimp [betaBinomialRawMoment]
  ring

theorem tendsto_betaBinomialGApproximation_coeff (a : ℝ) (ha : 0<a) (N ell : ℕ) :
    Tendsto (fun L : ℕ => (betaBinomialGApproximation a N L).coeff ell)
      atTop (𝓝 (betaBinomialGCoefficient a N ell)) :=
  tendsto_betaBinomial_derivativeApproximation_coeff a ha N ell

/-- Exact conversion from the two analytic coefficients to the normalized moment ratio. -/
theorem betaBinomial_coefficient_ratio (a : ℝ) (ha : 0<a) (N ell : ℕ) (hN : N ≠ 0) :
    betaBinomialFCoefficient a N ell / betaBinomialGCoefficient a N ell =
      (2*(ell:ℝ)+1) * (betaBinomialMoment N a ell / betaBinomialMoment N a (ell+1) - 1) := by
  have hn : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hp := (betaBinomialMoment_pos N hN a ha (ell+1)).ne'
  rw [betaBinomialFCoefficient, betaBinomialGCoefficient,
    betaBinomialRawMoment_eq_scaled a N ell hN,
    betaBinomialRawMoment_eq_scaled a N (ell+1) hN,
    Nat.factorial_succ]
  push_cast
  rw [show 2*(ell+1)=2*ell+2 by omega, pow_add]
  field_simp

/-- A limit of the actual finite approximations preserves the coefficient comparison.
The premise here is discharged by the concrete finite root theorem in the final module. -/
theorem betaBinomialMoment_ratio_of_approximation (a : ℝ) (ha : 0<a) (m ell : ℕ)
    (hcross : ∀ᶠ L : ℕ in atTop,
      (betaBinomialFApproximation a m L).coeff (ell+1) * (betaBinomialGApproximation a (m+2) L).coeff ell ≤
        (betaBinomialFApproximation a m L).coeff ell * (betaBinomialGApproximation a (m+2) L).coeff (ell+1)) :
    (2*((ell+1:ℕ):ℝ)+1) * (betaBinomialMoment (m+2) a (ell+1) / betaBinomialMoment (m+2) a (ell+2) - 1) ≤
      (2*(ell:ℝ)+1) * (betaBinomialMoment (m+2) a ell / betaBinomialMoment (m+2) a (ell+1) - 1) := by
  have hN : m+2 ≠ 0 := by omega
  have H : betaBinomialFCoefficient a (m+2) (ell+1) * betaBinomialGCoefficient a (m+2) ell ≤
      betaBinomialFCoefficient a (m+2) ell * betaBinomialGCoefficient a (m+2) (ell+1) := by
    apply le_of_tendsto_of_tendsto
      ((tendsto_betaBinomialFApproximation_coeff a ha m (ell+1)).mul
        (tendsto_betaBinomialGApproximation_coeff a ha (m+2) ell))
      ((tendsto_betaBinomialFApproximation_coeff a ha m ell).mul
        (tendsto_betaBinomialGApproximation_coeff a ha (m+2) (ell+1)))
    exact hcross
  have HR := (div_le_div_iff₀ (betaBinomialGCoefficient_pos a ha (m+2) (ell+1) hN)
    (betaBinomialGCoefficient_pos a ha (m+2) ell hN)).mpr H
  simpa only [betaBinomial_coefficient_ratio a ha (m+2) _ hN, Nat.add_assoc] using HR

end RenyiMonotonicity
