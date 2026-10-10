module

public import RenyiMonotonicity.CubicSplitting
public import RenyiMonotonicity.ContactSingleton
public import RenyiMonotonicity.ContactTwoRoots
public import RenyiMonotonicity.ContactStationarity

/-! Exact count-moment identities for the two stationary contact families. -/

@[expose] public section
noncomputable section
open scoped BigOperators
open Polynomial

namespace RenyiMonotonicity

/-- Multiplication by the count is the polynomial operator `X * derivative`. -/
theorem coeff_X_derivative (P : ℝ[X]) (k : ℕ) :
    (X * derivative P).coeff k = (k : ℝ) * P.coeff k := by
  cases k with
  | zero => simp
  | succ k => simp [coeff_derivative, mul_comm]

/-- The second factorial count moment is represented by the second derivative. -/
theorem coeff_X_sq_second_derivative (P : ℝ[X]) (k : ℕ) :
    (X^2 * derivative (derivative P)).coeff k =
      ((k : ℝ)^2 - k) * P.coeff k := by
  cases k with
  | zero => simp
  | succ k =>
    cases k with
    | zero => simp [pow_two, mul_assoc]
    | succ k =>
      simp only [pow_two, mul_assoc, coeff_X_mul, coeff_derivative]
      push_cast
      ring

/-- The actual quadratic mass moment is a polynomial-gradient pairing. -/
theorem quadraticMassMoment_polynomial {n : ℕ} (q : ℝ) (p : Fin n → ℝ) :
    quadraticMassMoment q n (bernoulliMass p) =
      polynomialGradientPairing q p
        (X * derivative (bernoulliPolynomial p) + X^2 * derivative (derivative (bernoulliPolynomial p))) := by
  unfold quadraticMassMoment massGradientPairing polynomialGradientPairing
  apply Finset.sum_congr rfl
  intro k _
  simp only [coeff_add, coeff_X_derivative, coeff_X_sq_second_derivative, bernoulliMass_natCast,
    bernoulliMassGradient]
  push_cast
  ring

/-- Stationarity annihilates the first polynomial count moment. -/
theorem polynomialGradientPairing_X_derivative_zero {n : ℕ} (q : ℝ) (p : Fin (n+1) → ℝ)
    (hp : ∀ i, 0 < p i) (hp₁ : ∀ i, p i < 1) (hD : midpointFunctional q p = 0)
    (hstat : ∀ i, deriv (fun t => midpointFunctional q (Function.update p i t)) (p i) = 0) :
    polynomialGradientPairing q p (X * derivative (bernoulliPolynomial p)) = 0 := by
  simpa only [polynomialGradientPairing, coeff_X_derivative, massGradientPairing,
    bernoulliMass_natCast, bernoulliMassGradient, Int.cast_natCast] using
    firstMassMoment_eq_zero_of_stationary q p hp hp₁ hD hstat

@[simp] theorem derivative_coinFactor (a : ℝ) : derivative (coinFactor a) = C a := by
  simp [coinFactor]

@[simp] theorem bernoulliPolynomial_const (n : ℕ) (a : ℝ) :
    bernoulliPolynomial (fun _ : Fin n => a) = coinFactor a ^ n := by
  simp [bernoulliPolynomial, coinFactor]

/-- Exact second derivative of a repeated Bernoulli factor. -/
theorem second_derivative_coinFactor_pow (a : ℝ) (n : ℕ) :
    derivative (derivative (coinFactor a ^ (n+2))) =
      C (((n+2 : ℕ) : ℝ) * (n+1) * a^2) * coinFactor a ^ n := by
  simp only [derivative_pow_succ, derivative_coinFactor, derivative_mul,
    derivative_C, zero_mul, zero_add, mul_zero, add_zero]
  push_cast
  simp only [map_mul, map_add, map_pow, map_ofNat, map_one]
  ring

/-- The analogous derivative with one distinct singleton factor. -/
theorem second_derivative_coinFactor_singleton (p a : ℝ) (n : ℕ) :
    derivative (derivative (coinFactor p ^ (n+2) * coinFactor a)) =
      C (((n+2 : ℕ) : ℝ) * (n+1) * p^2) * coinFactor p ^ n * coinFactor a +
      C (2 * (n+2 : ℕ) * p * a) * coinFactor p ^ (n+1) := by
  rw [derivative_mul, derivative_add, derivative_mul, derivative_mul,
    second_derivative_coinFactor_pow]
  simp only [derivative_coinFactor, derivative_C, mul_zero, add_zero, derivative_pow_succ]
  push_cast
  simp only [map_mul, map_add, map_pow, map_ofNat, map_one]
  ring

/-- Root evaluation gives the two polynomial identities needed for the singleton moment. -/
theorem linearMap_singleton_count_relations (L : ℝ[X] →ₗ[ℝ] ℝ) (p a : ℝ)
    (hp : p ≠ 0) (hm : ∀ j ≤ 3, L (X^j) = L 1 * coinRoot p ^ j) :
    L (X^2 * coinFactor p) = 0 ∧
      L (X^2 * coinFactor a) = (1-p)^2 * L ((X-1)^2 * coinFactor a) := by
  have he (Q : ℝ[X]) (hQ : Q.natDegree ≤ 3) : L Q = L 1 * Q.eval (coinRoot p) := by
    simpa using linearMap_eq_two_eval L (coinRoot p) 0 (L 1) 0 3
      (fun j hj => by simpa using hm j hj) Q hQ
  constructor
  · rw [he (X^2 * coinFactor p) (by unfold coinFactor; compute_degree)]
    simp [coinFactor_eval_root p hp]
  · rw [he (X^2 * coinFactor a) (by unfold coinFactor; compute_degree),
      he ((X-1)^2 * coinFactor a) (by unfold coinFactor; compute_degree)]
    simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_one]
    have hx : coinRoot p ^ 2 = (1-p)^2 * (coinRoot p-1)^2 := by
      unfold coinRoot
      field_simp
      ring
    rw [hx]
    ring

/-- Two elementary annihilations give the analogous pure-family count identity. -/
theorem linearMap_pure_count_relation (L : ℝ[X] →ₗ[ℝ] ℝ) (p : ℝ) (hp : p ≠ 0)
    (hP : L (coinFactor p ^ 2) = 0) (hO : L (coinFactor p) = 0) :
    L (X^2) = (1-p)^2 * L ((X-1)^2) := by
  have hw : L ((X-1)*coinFactor p) = 0 := by
    have H := linearMap_mul_coinFactor L (coinFactor p) p
    rw [← pow_two, hP, hO, zero_add] at H
    have H' := (mul_eq_zero.mp H.symm).resolve_left hp
    simpa only [mul_comm] using H'
  rw [show (X:ℝ[X])^2 = (1-p)^2 • (X-1)^2 +
      (2*(1-p)) • ((X-1)*coinFactor p) + coinFactor p^2 by
    simp only [coinFactor, smul_eq_C_mul, map_pow, map_sub, map_one, map_mul, map_ofNat]
    ring]
  simp only [map_add, map_smul, smul_eq_mul, hw, hP, mul_zero, add_zero]

end RenyiMonotonicity
