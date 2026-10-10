module

public import RenyiMonotonicity.ContactFamilyMoments
public import RenyiMonotonicity.OddsCurvature
public import RenyiMonotonicity.EscortContact

/-! Exclusion of the actual pure and singleton stationary contact families. -/

@[expose] public section
noncomputable section

namespace RenyiMonotonicity

/-- A pure binomial with at least three interior coins cannot be a zero contact minimum. -/
theorem no_pure_binomial_contact (m : ℕ) (q a : ℝ)
    (hq₀ : 0 < q) (hq₁ : q < 1) (ha : 0 < a) (haHalf : a < 1/2)
    (hD : midpointFunctional q (tripleCoins a a a (fun _ : Fin m => a)) = 0)
    (hstat : ∀ i, deriv (fun t => midpointFunctional q
      (Function.update (tripleCoins a a a (fun _ : Fin m => a)) i t))
      ((tripleCoins a a a (fun _ : Fin m => a)) i) = 0)
    (hmin : ∀ r : Fin (m+3) → ℝ, (∀ i, r i ∈ Set.Icc (0:ℝ) (1/2)) →
      midpointFunctional q (tripleCoins a a a (fun _ : Fin m => a)) ≤ midpointFunctional q r) : False := by
  let P := tripleCoins a a a (fun _ : Fin m => a)
  have hp : ∀ i, 0 < P i := fun i =>
    Fin.cases ha (fun i => Fin.cases ha (fun i => Fin.cases ha (fun _ => ha) i) i) i
  have hpHalf : ∀ i, P i < 1/2 := fun i =>
    Fin.cases haHalf (fun i => Fin.cases haHalf (fun i => Fin.cases haHalf (fun _ => haHalf) i) i) i
  have hM := quadraticMassMoment_pure_neg m q a hq₀ hq₁ ha haHalf hD hstat hmin
  have hC := cubicEdgeKernel_neg_of_stationary_minimum q P hq₀ hq₁ hp hpHalf hD hstat hmin hM
  exact no_bernoulli_contact_of_stationary_strict_moments q P hq₀ hq₁ hp (fun i => (hpHalf i).le)
    hD hstat hM hC

/-- A repeated interior group and one distinct singleton cannot be a zero contact minimum. -/
theorem no_singleton_binomial_contact (m : ℕ) (q p a : ℝ)
    (hq₀ : 0 < q) (hq₁ : q < 1) (hp : 0 < p) (hpHalf : p < 1/2)
    (ha : 0 < a) (haHalf : a ≤ 1/2) (hpa : p ≠ a)
    (hD : midpointFunctional q (tripleCoins p p a (fun _ : Fin m => p)) = 0)
    (hstat : ∀ i, deriv (fun t => midpointFunctional q
      (Function.update (tripleCoins p p a (fun _ : Fin m => p)) i t))
      ((tripleCoins p p a (fun _ : Fin m => p)) i) = 0)
    (hmin : ∀ r : Fin (m+3) → ℝ, (∀ i, r i ∈ Set.Icc (0:ℝ) (1/2)) →
      midpointFunctional q (tripleCoins p p a (fun _ : Fin m => p)) ≤ midpointFunctional q r) : False := by
  have hap := (stationary_singleton_lt_repeated q p a (fun _ : Fin m => p)
    hq₀ hq₁ hp hpHalf ha haHalf (fun _ => hp) (fun _ => hpHalf.le) hpa hD
    (fun i => hstat ⟨i.val,by omega⟩) hmin).1
  let P := tripleCoins p p a (fun _ : Fin m => p)
  have hpos : ∀ i, 0 < P i := fun i =>
    Fin.cases hp (fun i => Fin.cases hp (fun i => Fin.cases ha (fun _ => hp) i) i) i
  have hhalf : ∀ i, P i < 1/2 := fun i =>
    Fin.cases hpHalf (fun i => Fin.cases hpHalf (fun i => Fin.cases (hap.trans hpHalf) (fun _ => hpHalf) i) i) i
  have hM := quadraticMassMoment_singleton_neg m q p a hq₀ hq₁ hp hpHalf ha haHalf hpa hD hstat hmin
  have hC := cubicEdgeKernel_neg_of_stationary_minimum q P hq₀ hq₁ hpos hhalf hD hstat hmin hM
  exact no_bernoulli_contact_of_stationary_strict_moments q P hq₀ hq₁ hpos (fun i => (hhalf i).le)
    hD hstat hM hC

end RenyiMonotonicity
