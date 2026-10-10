module

public import RenyiMonotonicity.ContactMoments

/-! Strict quadratic mass moments for the actual classified contact families. -/

@[expose] public section
noncomputable section
open scoped BigOperators
open Polynomial

namespace RenyiMonotonicity

/-- Exact second count moment for a pure repeated-coin contact. -/
theorem quadraticMassMoment_pure_identity (m : ℕ) (q a : ℝ)
    (ha : 0 < a) (ha₁ : a < 1)
    (hD : midpointFunctional q (tripleCoins a a a (fun _ : Fin m => a)) = 0)
    (hstat : ∀ i, deriv (fun t => midpointFunctional q
      (Function.update (tripleCoins a a a (fun _ : Fin m => a)) i t))
      ((tripleCoins a a a (fun _ : Fin m => a)) i) = 0) :
    quadraticMassMoment q (m+3) (bernoulliMass (tripleCoins a a a (fun _ : Fin m => a))) =
      (m+3 : ℝ)*(m+2)*a^2*(1-a)^2 * polynomialGradientPairing q
        (tripleCoins a a a (fun _ : Fin m => a))
        (bernoulliPolynomial (Fin.cons a (fun _ : Fin m => a)) * (X-1)^2) := by
  let P := tripleCoins a a a (fun _ : Fin m => a)
  let h : Fin (m+1) → ℝ := Fin.cons a (fun _ : Fin m => a)
  let L := backgroundGradientLinearMap q P h
  have hp : ∀ i, 0 < P i := fun i => Fin.cases ha (fun i => Fin.cases ha (fun i => Fin.cases ha (fun _ => ha) i) i) i
  have hp₁ : ∀ i, P i < 1 := fun i => Fin.cases ha₁ (fun i => Fin.cases ha₁ (fun i => Fin.cases ha₁ (fun _ => ha₁) i) i) i
  have hpoly : bernoulliPolynomial P = coinFactor a^(m+3) := by
    simp only [P, tripleCoins, bernoulliPolynomial_cons, coinFactor, bernoulliPolynomial_const]
    ring
  have hbg : bernoulliPolynomial h = coinFactor a^(m+1) := by
    simp only [h, bernoulliPolynomial_cons, coinFactor, bernoulliPolynomial_const]
    ring
  have hP : L (coinFactor a^2) = 0 := by
    have H := polynomialGradientPairing_euler q P hp hp₁
    rw [hD, mul_zero] at H
    change polynomialGradientPairing q P (bernoulliPolynomial h * coinFactor a^2) = 0
    rw [hbg, show coinFactor a^(m+1)*coinFactor a^2=coinFactor a^(m+3) by ring, ← hpoly]
    exact H
  have hO : L (coinFactor a) = 0 := by
    have H := (bernoulliGradientPairing_omit_of_stationary q P hp hp₁ 0 hD (hstat 0)).1
    have H' := (polynomialGradientPairing_shift_eq q P (omitCoin P 0) 0).trans H
    simpa only [L, P, h, tripleCoins, omitCoin_cons_zero, pow_zero, mul_one, one_mul,
      bernoulliPolynomial_cons, coinFactor, backgroundGradientLinearMap, LinearMap.coe_mk,
      AddHom.coe_mk, mul_comm, mul_left_comm, mul_assoc] using H'
  have hc := linearMap_pure_count_relation L a ha.ne' hP hO
  have hfirst := polynomialGradientPairing_X_derivative_zero q P hp hp₁ hD hstat
  rw [quadraticMassMoment_polynomial, polynomialGradientPairing_add, hfirst, zero_add,
    hpoly, second_derivative_coinFactor_pow a (m+1)]
  rw [show X^2*(C (((m+1+2 : ℕ):ℝ)*(((m+1:ℕ):ℝ)+1)*a^2)*coinFactor a^(m+1)) =
      C (((m+1+2 : ℕ):ℝ)*(((m+1:ℕ):ℝ)+1)*a^2)*(bernoulliPolynomial h*X^2) by rw [hbg]; ring,
    polynomialGradientPairing_C_mul]
  change (((m+1+2 : ℕ):ℝ)*(((m+1:ℕ):ℝ)+1)*a^2)*L (X^2) = _
  rw [hc]
  change (((m+1+2 : ℕ):ℝ)*(((m+1:ℕ):ℝ)+1)*a^2)*((1-a)^2*L ((X-1)^2)) =
    (m+3:ℝ)*(m+2)*a^2*(1-a)^2*L ((X-1)^2)
  push_cast
  ring

/-- Root-evaluation moments derived from actual singleton stationarity. -/
theorem singleton_background_moments {m : ℕ} (q p a : ℝ) (h : Fin m → ℝ)
    (hp : 0 < p) (hp₁ : p < 1) (ha : 0 < a) (ha₁ : a < 1)
    (hh : ∀ i, 0 < h i) (hh₁ : ∀ i, h i < 1) (hpa : p ≠ a)
    (hD : midpointFunctional q (tripleCoins p p a h) = 0)
    (hstat : ∀ i, deriv (fun t => midpointFunctional q
      (Function.update (tripleCoins p p a h) i t)) ((tripleCoins p p a h) i) = 0) :
    ∀ j ≤ 3, backgroundGradientLinearMap q (tripleCoins p p a h) h (X^j) =
      backgroundGradientLinearMap q (tripleCoins p p a h) h 1 * coinRoot p^j := by
  let P := tripleCoins p p a h
  let L := backgroundGradientLinearMap q P h
  have hpos : ∀ i, 0 < P i := fun i => Fin.cases hp (fun i => Fin.cases hp (fun i => Fin.cases ha hh i) i) i
  have hone : ∀ i, P i < 1 := fun i => Fin.cases hp₁ (fun i => Fin.cases hp₁ (fun i => Fin.cases ha₁ hh₁ i) i) i
  have hz (i : Fin (m+3)) : polynomialGradientPairing q P (bernoulliPolynomial (omitCoin P i)) = 0 := by
    have H := (bernoulliGradientPairing_omit_of_stationary q P hpos hone i hD (hstat i)).1
    simpa only [pow_zero, mul_one, Nat.cast_zero] using
      (polynomialGradientPairing_shift_eq q P (omitCoin P i) 0).trans H
  have hA : L (coinFactor p*coinFactor a)=0 := by
    have H := hz 0
    simpa only [L,P,tripleCoins,omitCoin_cons_zero,bernoulliPolynomial_cons,coinFactor,
      backgroundGradientLinearMap,LinearMap.coe_mk,AddHom.coe_mk,mul_comm,mul_left_comm,mul_assoc] using H
  have hB : L (coinFactor p*coinFactor p)=0 := by
    have H := hz 2
    change polynomialGradientPairing q P (bernoulliPolynomial (omitCoin P ((0:Fin (m+1)).succ).succ))=0 at H
    simpa only [L,P,tripleCoins,omitCoin_cons_zero,omitCoin_cons_succ,bernoulliPolynomial_cons,coinFactor,
      backgroundGradientLinearMap,LinearMap.coe_mk,AddHom.coe_mk,mul_comm,mul_left_comm,mul_assoc] using H
  have hP : L (coinFactor p*coinFactor p*coinFactor a)=0 := by
    have H := polynomialGradientPairing_euler q P hpos hone
    rw [hD,mul_zero] at H
    simpa only [L,P,tripleCoins,bernoulliPolynomial_cons,coinFactor,
      backgroundGradientLinearMap,LinearMap.coe_mk,AddHom.coe_mk,mul_comm,mul_left_comm,mul_assoc] using H
  exact linearMap_repeated_singleton_moments L p a hp.ne' ha.ne' hpa hP hA hB

/-- Exact quadratic count moment for a repeated group and one singleton. -/
theorem quadraticMassMoment_singleton_identity (m : ℕ) (q p a : ℝ)
    (hp : 0 < p) (hp₁ : p < 1) (ha : 0 < a) (ha₁ : a < 1) (hpa : p ≠ a)
    (hD : midpointFunctional q (tripleCoins p p a (fun _ : Fin m => p)) = 0)
    (hstat : ∀ i, deriv (fun t => midpointFunctional q
      (Function.update (tripleCoins p p a (fun _ : Fin m => p)) i t))
      ((tripleCoins p p a (fun _ : Fin m => p)) i) = 0) :
    quadraticMassMoment q (m+3) (bernoulliMass (tripleCoins p p a (fun _ : Fin m => p))) =
      (m+2 : ℝ)*(m+1)*p^2*(1-p)^2 * polynomialGradientPairing q
        (tripleCoins p p a (fun _ : Fin m => p))
        (bernoulliPolynomial (Fin.cons a (fun _ : Fin m => p)) * (X-1)^2) := by
  let P := tripleCoins p p a (fun _ : Fin m => p)
  let h := fun _ : Fin m => p
  let L := backgroundGradientLinearMap q P h
  have hpos : ∀ i, 0 < P i := fun i => Fin.cases hp (fun i => Fin.cases hp (fun i => Fin.cases ha (fun _ => hp) i) i) i
  have hone : ∀ i, P i < 1 := fun i => Fin.cases hp₁ (fun i => Fin.cases hp₁ (fun i => Fin.cases ha₁ (fun _ => hp₁) i) i) i
  have hpoly : bernoulliPolynomial P = coinFactor p^(m+2)*coinFactor a := by
    simp only [P, tripleCoins, bernoulliPolynomial_cons, coinFactor, bernoulliPolynomial_const]
    ring
  have hbg : bernoulliPolynomial h = coinFactor p^m := bernoulliPolynomial_const m p
  have hm := singleton_background_moments q p a h hp hp₁ ha ha₁ (fun _ => hp) (fun _ => hp₁) hpa hD hstat
  have hc := linearMap_singleton_count_relations L p a hp.ne' hm
  have hfirst := polynomialGradientPairing_X_derivative_zero q P hpos hone hD hstat
  rw [quadraticMassMoment_polynomial, polynomialGradientPairing_add, hfirst, zero_add,
    hpoly, second_derivative_coinFactor_singleton]
  rw [show X^2*(C (((m+2 : ℕ):ℝ)*(m+1)*p^2)*coinFactor p^m*coinFactor a+
        C (2*(m+2:ℕ)*p*a)*coinFactor p^(m+1)) =
      C (((m+2 : ℕ):ℝ)*(m+1)*p^2)*(bernoulliPolynomial h*(X^2*coinFactor a))+
        C (2*(m+2:ℕ)*p*a)*(bernoulliPolynomial h*(X^2*coinFactor p)) by rw [hbg]; ring,
    polynomialGradientPairing_add, polynomialGradientPairing_C_mul, polynomialGradientPairing_C_mul]
  change (((m+2 : ℕ):ℝ)*(m+1)*p^2)*L (X^2*coinFactor a)+
    (2*(m+2:ℕ)*p*a)*L (X^2*coinFactor p) = _
  rw [hc.1, mul_zero, add_zero, hc.2]
  have hend : polynomialGradientPairing q P (bernoulliPolynomial (Fin.cons a h)*(X-1)^2) =
      L ((X-1)^2*coinFactor a) := by
    simp only [L, backgroundGradientLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
      bernoulliPolynomial_cons, coinFactor, mul_comm, mul_assoc]
  rw [hend]
  push_cast
  ring

/-- The pure-binomial quadratic count moment is strictly negative at contact. -/
theorem quadraticMassMoment_pure_neg (m : ℕ) (q a : ℝ)
    (hq₀ : 0 < q) (hq₁ : q < 1) (ha : 0 < a) (haHalf : a < 1/2)
    (hD : midpointFunctional q (tripleCoins a a a (fun _ : Fin m => a)) = 0)
    (hstat : ∀ i, deriv (fun t => midpointFunctional q
      (Function.update (tripleCoins a a a (fun _ : Fin m => a)) i t))
      ((tripleCoins a a a (fun _ : Fin m => a)) i) = 0)
    (hmin : ∀ r : Fin (m+3) → ℝ, (∀ i, r i ∈ Set.Icc (0:ℝ) (1/2)) →
      midpointFunctional q (tripleCoins a a a (fun _ : Fin m => a)) ≤ midpointFunctional q r) :
    quadraticMassMoment q (m+3) (bernoulliMass (tripleCoins a a a (fun _ : Fin m => a))) < 0 := by
  have h1a : 0 < 1-a := by linarith
  rw [quadraticMassMoment_pure_identity m q a ha (by linarith) hD hstat]
  exact mul_neg_of_pos_of_neg (by positivity)
    (polynomialGradientPairing_splitting_neg_three_equal q a (fun _ : Fin m => a)
      hq₀ hq₁ ha haHalf (fun _ => ha) (fun _ => haHalf.le) hD (hstat 0) hmin)

/-- The singleton-family quadratic count moment is strictly negative at contact. -/
theorem quadraticMassMoment_singleton_neg (m : ℕ) (q p a : ℝ)
    (hq₀ : 0 < q) (hq₁ : q < 1) (hp : 0 < p) (hpHalf : p < 1/2)
    (ha : 0 < a) (haHalf : a ≤ 1/2) (hpa : p ≠ a)
    (hD : midpointFunctional q (tripleCoins p p a (fun _ : Fin m => p)) = 0)
    (hstat : ∀ i, deriv (fun t => midpointFunctional q
      (Function.update (tripleCoins p p a (fun _ : Fin m => p)) i t))
      ((tripleCoins p p a (fun _ : Fin m => p)) i) = 0)
    (hmin : ∀ r : Fin (m+3) → ℝ, (∀ i, r i ∈ Set.Icc (0:ℝ) (1/2)) →
      midpointFunctional q (tripleCoins p p a (fun _ : Fin m => p)) ≤ midpointFunctional q r) :
    quadraticMassMoment q (m+3) (bernoulliMass (tripleCoins p p a (fun _ : Fin m => p))) < 0 := by
  have h1p : 0 < 1-p := by linarith
  rw [quadraticMassMoment_singleton_identity m q p a hp (by linarith) ha (by linarith) hpa hD hstat]
  exact mul_neg_of_pos_of_neg (by positivity)
    (stationary_singleton_lt_repeated q p a (fun _ : Fin m => p)
      hq₀ hq₁ hp hpHalf ha haHalf (fun _ => hp) (fun _ => hpHalf.le) hpa hD
      (fun i => hstat ⟨i.val,by omega⟩) hmin).2

end RenyiMonotonicity
