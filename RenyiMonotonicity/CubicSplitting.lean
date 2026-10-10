module

public import RenyiMonotonicity.ContactRemainder
public import RenyiMonotonicity.ContactSplitting

/-! Strict splitting curvature from the actual three-equal-coins perturbation. -/

@[expose] public section
noncomputable section
open Filter Topology Polynomial
open scoped BigOperators
namespace RenyiMonotonicity

def massThirdDifference (h : ℤ → ℝ) (k : ℤ) : ℝ :=
  h (k - 3) - 3 * h (k - 2) + 3 * h (k - 1) - h k

/-- The actual perturbation `(a+t,a+t,a-2t)` has exactly its quadratic and
cubic coefficient terms, before any derivative is taken. -/
theorem bernoulliMass_cubic_split {m : ℕ} (a t : ℝ) (h : Fin m → ℝ) (k : ℤ) :
    bernoulliMass (tripleCoins (a + t) (a + t) (a - 2 * t) h) k =
      bernoulliMass (tripleCoins a a a h) k -
        3 * t ^ 2 * massSecondDifference (bernoulliMass (Fin.cons a h)) k -
        2 * t ^ 3 * massThirdDifference (bernoulliMass h) k := by
  simp only [tripleCoins, bernoulliMass_cons, massSecondDifference, massThirdDifference]
  rw [show k - 1 - 1 = k - 2 by omega, show k - 2 - 1 = k - 3 by omega]
  ring

@[simp] theorem massThirdDifference_outer_left {m : ℕ} (h : Fin m → ℝ) :
    massThirdDifference (bernoulliMass h) (-1) = 0 := by
  norm_num [massThirdDifference, bernoulliMass_neg]

@[simp] theorem massThirdDifference_outer_right {m : ℕ} (h : Fin m → ℝ) :
    massThirdDifference (bernoulliMass h) ((m : ℤ) + 4) = 0 := by
  unfold massThirdDifference
  rw [bernoulliMass_eq_zero_above h _ (by omega), bernoulliMass_eq_zero_above h _ (by omega),
    bernoulliMass_eq_zero_above h _ (by omega), bernoulliMass_eq_zero_above h _ (by omega)]
  ring

theorem polynomialGradientPairing_thirdDifference {n m : ℕ} (q : ℝ)
    (p : Fin n → ℝ) (h : Fin m → ℝ) :
    polynomialGradientPairing q p (bernoulliPolynomial h * (X - 1) ^ 3) =
      massGradientPairing q n (bernoulliMass p) (massThirdDifference (bernoulliMass h)) := by
  rw [show bernoulliPolynomial h * (X - 1) ^ 3 =
      bernoulliPolynomial h * X ^ 3 - C 3 * (bernoulliPolynomial h * X ^ 2) +
        C 3 * (bernoulliPolynomial h * X ^ 1) - bernoulliPolynomial h * X ^ 0 by
    simp only [map_ofNat]; ring]
  simp only [polynomialGradientPairing_sub, polynomialGradientPairing_add,
    polynomialGradientPairing_C_mul, polynomialGradientPairing_shift_eq,
    bernoulliGradientPairing, massGradientPairing, massThirdDifference, Nat.cast_ofNat,
    Nat.cast_one, Nat.cast_zero, sub_zero]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Four annihilations at three equal nonzero factors force four consecutive
ordinary shifts to vanish. -/
theorem linearMap_cubic_repeated_factors (L : ℝ[X] →ₗ[ℝ] ℝ) (a : ℝ) (ha : a ≠ 0)
    (hP : L (coinFactor a * coinFactor a * coinFactor a) = 0)
    (hO : L (coinFactor a * coinFactor a) = 0)
    (hC : L ((X - 1) ^ 2 * coinFactor a) = 0)
    (hT : L ((X - 1) ^ 3) = 0) : ∀ j : Fin 4, L (X ^ j.val) = 0 := by
  have hsq : L ((X - 1) ^ 2) = 0 := by
    rw [show (X - 1) ^ 2 * coinFactor a = (X - 1) ^ 2 + a • ((X - 1) ^ 3) by
      rw [coinFactor_eq]; simp only [smul_eq_C_mul]; ring,
      map_add, map_smul, hT, smul_zero, add_zero] at hC
    exact hC
  rw [linearMap_coinFactor_pair, hsq, mul_zero, add_zero] at hO
  rw [linearMap_coinFactor_triple, hsq, hT, mul_zero, mul_zero, add_zero, add_zero] at hP
  have hlin : L (X - 1) = 0 := by
    exact (mul_eq_zero.mp (show a * L (X - 1) = 0 by linarith)).resolve_left ha
  have hconst : L 1 = 0 := by simpa [hlin] using hO
  exact linearMap_X_powers_zero L hconst hlin hsq hT

/-- The cubic mass coefficient vanishes at a three-coin contact if the
quadratic splitting coefficient vanishes. -/
theorem polynomialGradientPairing_cubic_split_zero {m : ℕ} (q a : ℝ) (h : Fin m → ℝ)
    (ha : 0 < a) (haHalf : a < 1 / 2) (hh : ∀ i, 0 < h i) (hhHalf : ∀ i, h i ≤ 1 / 2)
    (hmin : ∀ r : Fin (m + 3) → ℝ, (∀ i, r i ∈ Set.Icc (0 : ℝ) (1 / 2)) →
      midpointFunctional q (tripleCoins a a a h) ≤ midpointFunctional q r)
    (hC : polynomialGradientPairing q (tripleCoins a a a h)
      (bernoulliPolynomial (Fin.cons a h) * (X - 1) ^ 2) = 0) :
    polynomialGradientPairing q (tripleCoins a a a h) (bernoulliPolynomial h * (X - 1) ^ 3) = 0 := by
  let p := tripleCoins a a a h
  let u : ℤ → ℝ := fun k => -3 * massSecondDifference (bernoulliMass (Fin.cons a h)) k
  let v : ℤ → ℝ := fun k => -2 * massThirdDifference (bernoulliMass h) k
  have hp : ∀ i, 0 < p i := by
    intro i
    exact Fin.cases ha (fun i => Fin.cases ha (fun i => Fin.cases ha hh i) i) i
  have hp₁ : ∀ i, p i < 1 := by
    intro i
    exact Fin.cases (by change a < 1; linarith) (fun i => Fin.cases (by change a < 1; linarith)
      (fun i => Fin.cases (by change a < 1; linarith) (fun i => by change h i < 1; linarith [hhHalf i]) i) i) i
  have he (t : ℝ) : (fun k => bernoulliMass p k + t ^ 2 * u k + t ^ 3 * v k) =
      bernoulliMass (tripleCoins (a + t) (a + t) (a - 2 * t) h) := by
    funext k
    rw [bernoulliMass_cubic_split]
    unfold u v p
    ring
  have hlocal : IsLocalMin (fun t : ℝ => finiteMassFunctional q (m + 3)
      (fun k => bernoulliMass p k + t ^ 2 * u k + t ^ 3 * v k)) 0 := by
    let δ := min a (1 / 2 - a) / 3
    have hδ : 0 < δ := div_pos (lt_min ha (by linarith)) (by norm_num)
    have ht : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < δ := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using ht
    filter_upwards [ht] with t ht
    have hlo := (abs_lt.mp ht).1
    have hhi := (abs_lt.mp ht).2
    have hδa : 3 * δ ≤ a := by dsimp [δ]; linarith [min_le_left a (1 / 2 - a)]
    have hδb : 3 * δ ≤ 1 / 2 - a := by dsimp [δ]; linarith [min_le_right a (1 / 2 - a)]
    have hr : ∀ i, tripleCoins (a + t) (a + t) (a - 2 * t) h i ∈ Set.Icc (0 : ℝ) (1 / 2) := by
      intro i
      refine Fin.cases (by change 0 ≤ a + t ∧ a + t ≤ 1 / 2; constructor <;> linarith) (fun i => ?_) i
      refine Fin.cases (by change 0 ≤ a + t ∧ a + t ≤ 1 / 2; constructor <;> linarith) (fun i => ?_) i
      refine Fin.cases (by change 0 ≤ a - 2 * t ∧ a - 2 * t ≤ 1 / 2; constructor <;> linarith) (fun i => ?_) i
      exact ⟨(hh i).le, hhHalf i⟩
    simpa only [he, finiteMassFunctional_bernoulliMass, add_zero, mul_zero, sub_zero] using hmin _ hr
  have hU : massGradientPairing q (m + 3) (bernoulliMass p) u = 0 := by
    rw [polynomialGradientPairing_secondDifference] at hC
    simp only [massGradientPairing, u, mul_assoc, ← Finset.mul_sum]
    change -3 * massGradientPairing q (m + 3) (bernoulliMass p)
      (massSecondDifference (bernoulliMass (Fin.cons a h))) = 0
    rw [hC, mul_zero]
  have hV := cubicMassPairing_eq_zero_of_localMin q (m + 3) (bernoulliMass p) u v
    (edgeSum_pos p hp hp₁)
    (by simp [u, massSecondDifference_outer_left])
    (by
      change -3 * massSecondDifference (bernoulliMass (Fin.cons a h)) (((m + 3 : ℕ) : ℤ) + 1) = 0
      rw [show ((m + 3 : ℕ) : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) + 3 by omega, massSecondDifference_outer_right, mul_zero])
    (by simp [v])
    (by rw [show ((m + 3 : ℕ) : ℤ) + 1 = (m : ℤ) + 4 by omega]; simp [v]) hU hlocal
  rw [polynomialGradientPairing_thirdDifference]
  unfold v massGradientPairing at hV
  simp only [mul_assoc, ← Finset.mul_sum] at hV
  change -2 * massGradientPairing q (m + 3) (bernoulliMass p) (massThirdDifference (bernoulliMass h)) = 0 at hV
  linarith

/-- The splitting curvature is strictly negative at a zero stationary contact
with three equal interior coins. This includes every pure binomial with at least
three coins; the proof uses the actual cubic perturbation and four-shift theorem. -/
theorem polynomialGradientPairing_splitting_neg_three_equal {m : ℕ} (q a : ℝ) (h : Fin m → ℝ)
    (hq₀ : 0 < q) (hq₁ : q < 1) (ha : 0 < a) (haHalf : a < 1 / 2)
    (hh : ∀ i, 0 < h i) (hhHalf : ∀ i, h i ≤ 1 / 2)
    (hD : midpointFunctional q (tripleCoins a a a h) = 0)
    (hstat : deriv (fun t => midpointFunctional q (Function.update (tripleCoins a a a h) 0 t)) a = 0)
    (hmin : ∀ r : Fin (m + 3) → ℝ, (∀ i, r i ∈ Set.Icc (0 : ℝ) (1 / 2)) →
      midpointFunctional q (tripleCoins a a a h) ≤ midpointFunctional q r) :
    polynomialGradientPairing q (tripleCoins a a a h)
      (bernoulliPolynomial (Fin.cons a h) * (X - 1) ^ 2) < 0 := by
  have hnonpos := polynomialGradientPairing_splitting_nonpos q a (Fin.cons a h) ha haHalf
    (fun i => Fin.cases ha hh i) (fun i => Fin.cases haHalf.le hhHalf i) hmin
  apply lt_of_le_of_ne hnonpos
  intro hEq
  have hC := hEq
  have hT := polynomialGradientPairing_cubic_split_zero q a h ha haHalf hh hhHalf hmin hC
  let p := tripleCoins a a a h
  let L := backgroundGradientLinearMap q p h
  have hp : ∀ i, 0 < p i := by
    intro i
    exact Fin.cases ha (fun i => Fin.cases ha (fun i => Fin.cases ha hh i) i) i
  have hpHalf : ∀ i, p i ≤ 1 / 2 := by
    intro i
    exact Fin.cases haHalf.le (fun i => Fin.cases haHalf.le (fun i => Fin.cases haHalf.le hhHalf i) i) i
  have hp₁ : ∀ i, p i < 1 := fun i => lt_of_le_of_lt (hpHalf i) (by norm_num)
  have hP : L (coinFactor a * coinFactor a * coinFactor a) = 0 := by
    have H := polynomialGradientPairing_euler q p hp hp₁
    rw [hD, mul_zero] at H
    simpa only [L, p, tripleCoins, bernoulliPolynomial_cons, coinFactor, backgroundGradientLinearMap,
      LinearMap.coe_mk, AddHom.coe_mk, mul_comm, mul_left_comm, mul_assoc] using H
  have hO : L (coinFactor a * coinFactor a) = 0 := by
    have H := (bernoulliGradientPairing_omit_of_stationary q p hp hp₁ 0 hD hstat).1
    have H' := (polynomialGradientPairing_shift_eq q p (omitCoin p 0) 0).trans H
    simpa only [L, p, tripleCoins, omitCoin_cons_zero, pow_zero, mul_one, one_mul, bernoulliPolynomial_cons,
      coinFactor, backgroundGradientLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
      mul_comm, mul_left_comm, mul_assoc] using H'
  have hC' : L ((X - 1) ^ 2 * coinFactor a) = 0 := by
    simpa only [L, p, pairCoins, tripleCoins, bernoulliPolynomial_cons, coinFactor, backgroundGradientLinearMap,
      LinearMap.coe_mk, AddHom.coe_mk, mul_comm, mul_left_comm, mul_assoc] using hC
  have hT' : L ((X - 1) ^ 3) = 0 := hT
  have hall := linearMap_cubic_repeated_factors L a ha.ne' hP hO hC' hT'
  obtain ⟨j, hj⟩ := polynomialGradientPairing_four_shifts_nonzero q p h hq₀ hq₁ hp hpHalf hh
    (fun i => lt_of_le_of_lt (hhHalf i) (by norm_num))
  exact hj (hall j)

end RenyiMonotonicity
